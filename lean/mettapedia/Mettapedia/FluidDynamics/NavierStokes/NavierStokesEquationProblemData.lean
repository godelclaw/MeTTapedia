import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationKits

/-!
# Concrete Navier-Stokes Problem Data and Clauses

This module packages problem data, witnesses, global regularity clauses,
explicit concrete targets, and repaired finite-energy target surfaces.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section ConcreteEquationTarget

open scoped Laplacian ContDiff

/-- Smooth divergence-free initial data together with a positive viscosity. -/
structure NavierStokesProblemData (D : NavierStokesDifferentialKit) where
  viscosity : ℝ
  viscosity_pos : 0 < viscosity
  initialVelocity : NSInitialVelocity
  smooth_initial : D.smoothInitialData initialVelocity
  divergence_free_initial : D.divergenceFreeInitialData initialVelocity

/-- Pointwise momentum equation `∂ₜ u + (u · ∇)u + ∇p = ν Δu`. -/
def SatisfiesMomentumEquation
    (D : NavierStokesDifferentialKit) (ν : ℝ)
    (u : NSVelocityField) (p : NSPressureField) : Prop :=
  ∀ t x,
    D.timeDerivative u t x + D.convection u t x + D.pressureGradient p t x =
      ν • D.laplacian u t x

/-- Pointwise incompressibility `div u = 0`. -/
def IsIncompressible
    (D : NavierStokesDifferentialKit) (u : NSVelocityField) : Prop :=
  ∀ t x, D.divergence u t x = 0

/-- Initial condition `u(0, ·) = u₀`. -/
def MatchesInitialVelocity
    (u₀ : NSInitialVelocity) (u : NSVelocityField) : Prop :=
  ∀ x, u 0 x = u₀ x

/-- Concrete global-regularity witness for the local NS target. -/
structure NavierStokesGlobalRegularityWitness
    (D : NavierStokesDifferentialKit) (P : NavierStokesProblemData D) where
  velocity : NSVelocityField
  pressure : NSPressureField
  smooth_velocity : D.smoothVelocity velocity
  smooth_pressure : D.smoothPressure pressure
  momentum_equation :
    SatisfiesMomentumEquation D P.viscosity velocity pressure
  incompressible : IsIncompressible D velocity
  initial_condition : MatchesInitialVelocity P.initialVelocity velocity
  bounded_energy : D.boundedEnergy velocity

/-- Concrete existence clause for the local NS target. -/
def NavierStokesGlobalRegularityClause
    (D : NavierStokesDifferentialKit) (P : NavierStokesProblemData D) : Prop :=
  Nonempty (NavierStokesGlobalRegularityWitness D P)

/-- First local theorem target mirroring the shape of the Clay/Fefferman
problem: every admissible initial datum has a global regularity witness. -/
def NavierStokesMillenniumTarget
    (D : NavierStokesDifferentialKit) : Prop :=
  ∀ P : NavierStokesProblemData D, NavierStokesGlobalRegularityClause D P

/-- Fully concrete local theorem target: smooth divergence-free initial data on
`ℝ^3` with positive viscosity have a global smooth incompressible solution with
bounded kinetic energy on `ℝ × ℝ^3`. -/
def ConcreteNavierStokesMillenniumTarget : Prop :=
  NavierStokesMillenniumTarget mkFullyConcreteNavierStokesSurface

/-- Fully explicit concrete global-regularity clause for fixed viscosity and
initial data on `ℝ^3`. -/
def ExplicitConcreteNavierStokesRegularityClause
    (ν : ℝ) (u₀ : NSInitialVelocity) : Prop :=
  0 < ν →
    smoothInitialVelocityData u₀ →
      (∀ x, initialSpatialDivergence u₀ x = 0) →
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

/-- Fully explicit local whole-space surrogate theorem target: every smooth
divergence-free initial velocity on `ℝ^3` and every positive viscosity have a
global smooth incompressible solution with uniformly bounded kinetic energy.
This is deliberately stronger than the manuscript-compatible restricted
whole-space surfaces considered later, so Lean keeps it as a regression target
for theorem-shape errors rather than as the final intended statement. -/
def ExplicitConcreteNavierStokesMillenniumTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity,
    ExplicitConcreteNavierStokesRegularityClause ν u₀

/-- Repaired concrete problem data: smooth divergence-free initial velocity on
`ℝ^3` with positive viscosity and finite initial kinetic energy. -/
structure FiniteEnergyAdmissibleNavierStokesProblemData where
  viscosity : ℝ
  viscosity_pos : 0 < viscosity
  initialVelocity : NSInitialVelocity
  smooth_initial : smoothInitialVelocityData initialVelocity
  divergence_free_initial : ∀ x, initialSpatialDivergence initialVelocity x = 0
  finite_initial_energy : finiteInitialKineticEnergy initialVelocity

/-- Forget the finite-energy witness and view repaired concrete problem data on
the existing fully concrete theorem surface. -/
def FiniteEnergyAdmissibleNavierStokesProblemData.toNavierStokesProblemData
    (P : FiniteEnergyAdmissibleNavierStokesProblemData) :
    NavierStokesProblemData mkFullyConcreteNavierStokesSurface where
  viscosity := P.viscosity
  viscosity_pos := P.viscosity_pos
  initialVelocity := P.initialVelocity
  smooth_initial := P.smooth_initial
  divergence_free_initial := P.divergence_free_initial

/-- Repaired structured whole-space theorem target: every smooth divergence-free
finite-energy initial datum admits a global regularity witness. -/
def FiniteEnergyConcreteNavierStokesMillenniumTarget : Prop :=
  ∀ P : FiniteEnergyAdmissibleNavierStokesProblemData,
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      P.toNavierStokesProblemData

/-- Repaired fully explicit global-regularity clause for fixed viscosity and
initial data on `ℝ^3`: the input side now explicitly requires finite initial
kinetic energy. -/
def ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
    (ν : ℝ) (u₀ : NSInitialVelocity) : Prop :=
  0 < ν →
    smoothInitialVelocityData u₀ →
      (∀ x, initialSpatialDivergence u₀ x = 0) →
        finiteInitialKineticEnergy u₀ →
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

/-- Repaired explicit theorem target: every smooth divergence-free finite-energy
initial velocity on `ℝ^3` and every positive viscosity have a global smooth
incompressible solution with uniformly bounded kinetic energy.  This is the
current local whole-space surface intended to stay compatible with reasonable
restricted `ℝ^3` routes, rather than the over-broad surrogate above. -/
def ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity,
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀

end ConcreteEquationTarget

end NavierStokes
end FluidDynamics
end Mettapedia
