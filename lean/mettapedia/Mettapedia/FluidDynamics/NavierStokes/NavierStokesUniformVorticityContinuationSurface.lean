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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Uniform-Vorticity Continuation Surface

This module contains the reusable finite-time witness, global-output, and
uniform-vorticity continuation clauses for the concrete `ℝ × ℝ^3`
Navier--Stokes surface.  Example fields, obstruction families, and regression
harnesses belong in downstream modules.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- Uniform kinetic-energy control on the slab `0 ≤ t ≤ T`. -/
def boundedKineticEnergyUpTo (u : NSVelocityField) (T : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → t ≤ T →
    MeasureTheory.Integrable (kineticEnergyDensity u t) ∧ kineticEnergyAt u t ≤ C

/-- Uniform vorticity bound on the slab `0 ≤ t ≤ T`. -/
def uniformVorticityBoundUpTo (u : NSVelocityField) (T B : ℝ) : Prop :=
  0 ≤ B ∧ ∀ t x, 0 ≤ t → t ≤ T → ‖spatialVorticity u t x‖ ≤ B

/-- Explicit finite-time smooth Navier--Stokes witness on the slab `0 ≤ t ≤ T`.
-/
structure ExplicitFiniteTimeRegularityWitness
    (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ) where
  velocity : NSVelocityField
  pressure : NSPressureField
  smooth_velocity : smoothSpaceTimeVelocity velocity
  smooth_pressure : smoothSpaceTimePressure pressure
  momentum_equation_on :
    ∀ t x, 0 ≤ t → t ≤ T →
      timeVelocityDerivative velocity t x + spatialConvection velocity t x +
          spatialPressureGradient pressure t x =
        ν • spatialLaplacian velocity t x
  incompressible_on :
    ∀ t x, 0 ≤ t → t ≤ T → spatialDivergence velocity t x = 0
  initial_condition : MatchesInitialVelocity u₀ velocity
  bounded_energy_on : boundedKineticEnergyUpTo velocity T

/-- On any certified time slice of a finite-time witness, the witness pressure
gradient is exactly the pressure residual of the witness velocity. -/
theorem ExplicitFiniteTimeRegularityWitness.pressureGradientVelocityField_eq_momentumPressureResidual_on
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    {t : NSTime} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∀ y : NSSpace,
      pressureGradientVelocityField W.pressure t y =
        momentumPressureResidual ν W.velocity t y := by
  intro y
  have hmom :
      timeVelocityDerivative W.velocity t y + spatialConvection W.velocity t y +
          spatialPressureGradient W.pressure t y =
        ν • spatialLaplacian W.velocity t y :=
    W.momentum_equation_on t y ht0 htT
  unfold pressureGradientVelocityField momentumPressureResidual
  calc
    spatialPressureGradient W.pressure t y =
        (timeVelocityDerivative W.velocity t y + spatialConvection W.velocity t y +
          spatialPressureGradient W.pressure t y) -
            timeVelocityDerivative W.velocity t y -
              spatialConvection W.velocity t y := by
      abel
    _ = ν • spatialLaplacian W.velocity t y -
          timeVelocityDerivative W.velocity t y -
            spatialConvection W.velocity t y := by
      rw [hmom]

/-- Every certified finite-time witness has curl-free pressure residual on its
certified time slab. -/
theorem ExplicitFiniteTimeRegularityWitness.spatialVorticity_momentumPressureResidual_zero_on
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    spatialVorticity (momentumPressureResidual ν W.velocity) t x = 0 := by
  calc
    spatialVorticity (momentumPressureResidual ν W.velocity) t x =
        spatialVorticity (pressureGradientVelocityField W.pressure) t x :=
      (spatialVorticity_congr_at
        (ExplicitFiniteTimeRegularityWitness.pressureGradientVelocityField_eq_momentumPressureResidual_on
          (ν := ν) (T := T) (u₀ := u₀) W ht0 htT)).symm
    _ = 0 := spatialVorticity_pressureGradientVelocityField W.smooth_pressure t x

/-- Transport the finite-time residual-curl necessary condition across a chosen
velocity equality. -/
theorem ExplicitFiniteTimeRegularityWitness.spatialVorticity_momentumPressureResidual_of_velocity_eq_zero_on
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hWvel : W.velocity = u)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    spatialVorticity (momentumPressureResidual ν u) t x = 0 := by
  simpa [← hWvel] using
    (ExplicitFiniteTimeRegularityWitness.spatialVorticity_momentumPressureResidual_zero_on
      (ν := ν) (T := T) (u₀ := u₀) W (t := t) (x := x) ht0 htT)

/-- A finite-time witness cannot realize a velocity whose exact pressure
residual has nonzero curl somewhere on the certified slab.  This is independent
of any pressure ansatz: the witness pressure is smooth, so its spatial gradient
is curl-free on each time slice. -/
theorem not_exists_ExplicitFiniteTimeRegularityWitness_velocity_of_momentumPressureResidual_vorticity_ne_zero_on
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      0 ≤ t ∧ t ≤ T ∧
        spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u := by
  rintro ⟨W, hWvel⟩
  rcases hcurl with ⟨t, x, ht0, htT, hne⟩
  exact hne
    (ExplicitFiniteTimeRegularityWitness.spatialVorticity_momentumPressureResidual_of_velocity_eq_zero_on
      (ν := ν) (T := T) (u₀ := u₀) W hWvel (t := t) (x := x) ht0 htT)

/-- Fully explicit global-output proposition for the concrete NS theorem surface.
-/
def ExplicitConcreteNavierStokesGlobalOutput
    (ν : ℝ) (u₀ : NSInitialVelocity) : Prop :=
  ∃ u : NSVelocityField, ∃ p : NSPressureField,
    smoothSpaceTimeVelocity u ∧
    smoothSpaceTimePressure p ∧
    (∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian u t x) ∧
    (∀ t x, spatialDivergence u t x = 0) ∧
    MatchesInitialVelocity u₀ u ∧
    boundedKineticEnergy u

/-- Explicit global-output proposition with the velocity field fixed in
advance.  This is the reusable surface for blocking a proposed candidate
velocity without choosing any pressure ansatz. -/
def ExplicitConcreteNavierStokesGlobalOutputWithVelocity
    (ν : ℝ) (u₀ : NSInitialVelocity) (u : NSVelocityField) : Prop :=
  ∃ p : NSPressureField,
    smoothSpaceTimeVelocity u ∧
    smoothSpaceTimePressure p ∧
    (∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian u t x) ∧
    (∀ t x, spatialDivergence u t x = 0) ∧
    MatchesInitialVelocity u₀ u ∧
    boundedKineticEnergy u

/-- The original global-output proposition is exactly the existential closure
of the prescribed-velocity version. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_iff_exists_velocity
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ ↔
      ∃ u : NSVelocityField,
        ExplicitConcreteNavierStokesGlobalOutputWithVelocity ν u₀ u := by
  rfl

/-- Any prescribed-velocity global output has curl-free exact pressure residual
at every spacetime point. -/
theorem ExplicitConcreteNavierStokesGlobalOutputWithVelocity.spatialVorticity_momentumPressureResidual_zero
    {ν : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (h : ExplicitConcreteNavierStokesGlobalOutputWithVelocity ν u₀ u)
    (t : NSTime) (x : NSSpace) :
    spatialVorticity (momentumPressureResidual ν u) t x = 0 := by
  rcases h with ⟨p, _hu, hp, hmom, _hdiv, _hinit, _henergy⟩
  exact spatialVorticity_momentumPressureResidual_of_momentumEquation hp hmom t x

/-- A velocity whose exact pressure residual has nonzero curl cannot be the
velocity component of any explicit global output. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutputWithVelocity_of_momentumPressureResidual_vorticity_ne_zero
    {ν : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocity ν u₀ u := by
  intro h
  rcases hcurl with ⟨t, x, hne⟩
  exact hne
    (ExplicitConcreteNavierStokesGlobalOutputWithVelocity.spatialVorticity_momentumPressureResidual_zero
      (ν := ν) (u₀ := u₀) (u := u) h t x)

/-- A concrete explicit global output immediately yields the corresponding
unrepaired explicit whole-space regularity clause. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitConcreteNavierStokesRegularityClause
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀) :
    ExplicitConcreteNavierStokesRegularityClause ν u₀ := by
  intro _hν _hsmooth _hdiv
  exact h

/-- A concrete explicit global output also yields the repaired explicit
whole-space regularity clause, since the extra finite-energy hypothesis only
narrows the admissible input data. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ := by
  intro _hν _hsmooth _hdiv _hfinite
  exact h

/-- A concrete explicit global output can be repackaged directly as the
structured fully concrete clause on the same datum. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_implies_concreteNavierStokesGlobalRegularityClause
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := u₀
        smooth_initial := hsmooth
        divergence_free_initial := hdiv } := by
  exact
    (concreteNavierStokesGlobalRegularityClause_iff
      (ν := ν) (u₀ := u₀) hν hsmooth hdiv).mpr h

/-- On a finite-energy datum, a concrete explicit global output can likewise be
repackaged directly as the repaired structured fully concrete clause. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_implies_finiteEnergyConcreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (h : ExplicitConcreteNavierStokesGlobalOutput ν u₀) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := u₀
         smooth_initial := hsmooth
         divergence_free_initial := hdiv
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    (finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
      hν hsmooth hdiv hfinite).mpr
      (ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        h)

/-- Concrete uniform-vorticity continuation clause: a finite-time smooth witness
with bounded vorticity on `0 ≤ t ≤ T` extends to a global smooth witness. -/
def ExplicitUniformVorticityContinuationClause
    (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ) : Prop :=
  0 < ν →
    smoothInitialVelocityData u₀ →
      (∀ x, initialSpatialDivergence u₀ x = 0) →
        ∀ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
          (∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) →
            ExplicitConcreteNavierStokesGlobalOutput ν u₀

/-- Global continuation target built from the concrete uniform-vorticity clause.
-/
def ExplicitUniformVorticityContinuationTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity, ∀ T : ℝ,
    ExplicitUniformVorticityContinuationClause ν u₀ T

/-- Repaired uniform-vorticity continuation clause: the concrete continuation
surface is restricted to smooth divergence-free initial data with finite
initial kinetic energy on `ℝ^3`. -/
def ExplicitFiniteEnergyUniformVorticityContinuationClause
    (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ) : Prop :=
  0 < ν →
    smoothInitialVelocityData u₀ →
      (∀ x, initialSpatialDivergence u₀ x = 0) →
        finiteInitialKineticEnergy u₀ →
          ∀ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
            (∃ B : ℝ, uniformVorticityBoundUpTo W.velocity T B) →
              ExplicitConcreteNavierStokesGlobalOutput ν u₀

/-- Global repaired continuation target built from the finite-energy
uniform-vorticity clause. -/
def ExplicitFiniteEnergyUniformVorticityContinuationTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity, ∀ T : ℝ,
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T

/-- Corrected repaired continuation target: only nonnegative horizons are
admissible. This rules out the degenerate negative-horizon witness loophole
while retaining the intended finite-energy continuation surface. -/
def ExplicitFiniteEnergyUniformVorticityContinuationTargetOnNonnegHorizons : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity, ∀ ⦃T : ℝ⦄,
    0 ≤ T → ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T

/-- The repaired uniform-vorticity continuation clause is vacuous outside the
finite-energy input domain: once `u₀` fails the repaired hypothesis, the clause
holds for purely logical reasons. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (hfinite : ¬ finiteInitialKineticEnergy u₀) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν u₀ T := by
  intro _hν _hsmooth _hdiv hE _W _hω
  exact False.elim (hfinite hE)

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
