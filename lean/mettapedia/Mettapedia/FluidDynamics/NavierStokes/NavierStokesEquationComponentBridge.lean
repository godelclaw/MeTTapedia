import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationProblemData

/-!
# Component Bridge from Vector Navier-Stokes to Scalar Fefferman Surfaces

This module maps a full vector-valued Navier-Stokes witness to coordinatewise
scalar Fefferman-style output shells.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section ConcreteEquationTarget

open scoped Laplacian ContDiff

/-- Scalar component of a vector-valued velocity field. -/
def velocityComponent (u : NSVelocityField) (i : Fin 3) : NSScalarField :=
  fun t x => u t x i

/-- Componentwise scalar shadow of the concrete vector-valued NS target.  This
is the honest meeting point with the current scalar Fefferman bridge surface. -/
def NavierStokesDifferentialKit.toComponentPredicateKit
    (D : NavierStokesDifferentialKit) (P : NavierStokesProblemData D) (i : Fin 3) :
    FeffermanPredicateKit (Time := NSTime) (X := NSSpace) where
  SmoothVelocity := fun u =>
    ∃ U : NSVelocityField, D.smoothVelocity U ∧ velocityComponent U i = u
  SmoothPressure := D.smoothPressure
  MomentumEquation := fun u p =>
    ∃ U : NSVelocityField,
      D.smoothVelocity U ∧
      velocityComponent U i = u ∧
      SatisfiesMomentumEquation D P.viscosity U p
  Incompressible := fun u =>
    ∃ U : NSVelocityField, IsIncompressible D U ∧ velocityComponent U i = u
  InitialCondition := fun u =>
    ∃ U : NSVelocityField,
      MatchesInitialVelocity P.initialVelocity U ∧ velocityComponent U i = u
  BoundedEnergy := fun u =>
    ∃ U : NSVelocityField, D.boundedEnergy U ∧ velocityComponent U i = u

/-- Any full NS witness yields a scalar component witness for the current
Fefferman-style output shell. -/
def NavierStokesGlobalRegularityWitness.toComponentFeffermanOutput
    {D : NavierStokesDifferentialKit} {P : NavierStokesProblemData D}
    (W : NavierStokesGlobalRegularityWitness D P) (i : Fin 3) :
    FeffermanGlobalRegularityOutput (D.toComponentPredicateKit P i) where
  velocity := velocityComponent W.velocity i
  pressure := W.pressure
  smooth_velocity := ⟨W.velocity, W.smooth_velocity, rfl⟩
  smooth_pressure := W.smooth_pressure
  momentum_equation := ⟨W.velocity, W.smooth_velocity, rfl, W.momentum_equation⟩
  incompressible := ⟨W.velocity, W.incompressible, rfl⟩
  initial_condition := ⟨W.velocity, W.initial_condition, rfl⟩
  bounded_energy := ⟨W.velocity, W.bounded_energy, rfl⟩

/-- Therefore a full vector-valued NS clause implies the scalar component shadow
seen by the current route. -/
theorem NavierStokesGlobalRegularityClause.implies_componentFeffermanClause
    {D : NavierStokesDifferentialKit} {P : NavierStokesProblemData D}
    (h : NavierStokesGlobalRegularityClause D P) (i : Fin 3) :
    FeffermanGlobalRegularityClause (D.toComponentPredicateKit P i) := by
  rcases h with ⟨W⟩
  exact ⟨W.toComponentFeffermanOutput i⟩

/-- Likewise, a full theorem target immediately implies the component-level
Fefferman-style target for every coordinate. -/
theorem NavierStokesMillenniumTarget.implies_componentFeffermanTarget
    {D : NavierStokesDifferentialKit}
    (h : NavierStokesMillenniumTarget D) (i : Fin 3) :
    ∀ P : NavierStokesProblemData D,
      FeffermanGlobalRegularityClause (D.toComponentPredicateKit P i) := by
  intro P
  exact (NavierStokesGlobalRegularityClause.implies_componentFeffermanClause
    (D := D) (P := P) (h P) i)

end ConcreteEquationTarget

end NavierStokes
end FluidDynamics
end Mettapedia
