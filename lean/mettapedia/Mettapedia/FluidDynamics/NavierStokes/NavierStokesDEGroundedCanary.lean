import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionZero
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyZero
import Mathlib.Tactic

/-!
# DE-grounded Navier-Stokes canary

This module records a non-vacuous baseline for the concrete `ℝ × ℝ^3`
Navier-Stokes surface.  It does not claim global regularity.  It packages the
zero velocity/pressure solution, its corrected energy identity, and the standard
three-dimensional scaling arithmetic used to keep finite-energy promotion
honest.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory

section ConcreteDEGrounding

/-- Concrete positive-viscosity zero-data problem used as the DE-grounded
positive canary. -/
def concreteNSZeroProblemData :
    NavierStokesProblemData mkFullyConcreteNavierStokesSurface where
  viscosity := 1
  viscosity_pos := by norm_num
  initialVelocity := 0
  smooth_initial := smoothInitialVelocityData_zero
  divergence_free_initial := by
    intro x
    simpa using (initialSpatialDivergence_zero x)

/-- The actual zero velocity/pressure fields solve the fully concrete
Navier-Stokes momentum equation at viscosity `1`. -/
theorem concreteNSZero_momentumEquation :
    SatisfiesMomentumEquation
      mkFullyConcreteNavierStokesSurface
      1
      (0 : NSVelocityField)
      (0 : NSPressureField) := by
  intro t x
  simpa [SatisfiesMomentumEquation, mkFullyConcreteNavierStokesSurface] using
    momentumEquation_zeroVelocityField_zeroPressure (1 : ℝ) t x

/-- The zero velocity field is incompressible for the fully concrete
Navier-Stokes surface. -/
theorem concreteNSZero_incompressible :
    IsIncompressible
      mkFullyConcreteNavierStokesSurface
      (0 : NSVelocityField) := by
  intro t x
  simpa [IsIncompressible, mkFullyConcreteNavierStokesSurface] using
    spatialDivergence_zero t x

/-- The zero field satisfies the zero initial condition. -/
theorem concreteNSZero_initialCondition :
    MatchesInitialVelocity (0 : NSInitialVelocity) (0 : NSVelocityField) := by
  intro x
  rfl

/-- The zero velocity field has bounded kinetic energy on every time slice. -/
theorem concreteNSZero_boundedEnergy :
    boundedKineticEnergy (0 : NSVelocityField) := by
  exact
    (zeroNavierStokesGlobalRegularityWitness
      (ν := (1 : ℝ)) (by norm_num)).bounded_energy

/-- The fully concrete zero-data global witness. -/
def concreteNSZeroGlobalRegularityWitness :
    NavierStokesGlobalRegularityWitness
      mkFullyConcreteNavierStokesSurface
      concreteNSZeroProblemData where
  velocity := 0
  pressure := 0
  smooth_velocity := by
    simpa [mkFullyConcreteNavierStokesSurface] using
      smoothSpaceTimeVelocity_zero
  smooth_pressure := by
    simpa [mkFullyConcreteNavierStokesSurface] using
      smoothSpaceTimePressure_zero
  momentum_equation := concreteNSZero_momentumEquation
  incompressible := concreteNSZero_incompressible
  initial_condition := concreteNSZero_initialCondition
  bounded_energy := concreteNSZero_boundedEnergy

/-- The concrete DE-grounded global-regularity clause is inhabited at zero data.
This is only a positive canary for the theorem surface, not a general theorem. -/
theorem concreteNSZero_globalRegularityClause :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      concreteNSZeroProblemData := by
  exact ⟨concreteNSZeroGlobalRegularityWitness⟩

/-- The zero datum is an inhabited repaired finite-energy input. -/
theorem concreteNSZero_finiteInitialEnergy :
    finiteInitialKineticEnergy (0 : NSInitialVelocity) :=
  finiteInitialKineticEnergy_zero

/-- The zero solution satisfies the guarded coordinate energy identity. -/
theorem concreteNSZero_coordinateEnergyIdentity :
    ∀ t,
      Integrable (kineticEnergyDensity (0 : NSVelocityField) t)
        (volume : Measure NSSpace) ∧
        HasDerivAt (normalizedKineticEnergy (0 : NSVelocityField))
          (-(coordinateEnergyDissipationRate (0 : NSVelocityField) 1 t)) t := by
  exact meaningfulCoordinateEnergyDissipationIdentity_smooth_zero (1 : ℝ)

/-- Positive canary package for the fully concrete DE surface. -/
structure ConcreteNSZeroCanary where
  finiteInitialEnergy :
    finiteInitialKineticEnergy (0 : NSInitialVelocity)
  momentumEquation :
    SatisfiesMomentumEquation
      mkFullyConcreteNavierStokesSurface
      1
      (0 : NSVelocityField)
      (0 : NSPressureField)
  incompressible :
    IsIncompressible
      mkFullyConcreteNavierStokesSurface
      (0 : NSVelocityField)
  initialCondition :
    MatchesInitialVelocity (0 : NSInitialVelocity) (0 : NSVelocityField)
  boundedEnergy :
    boundedKineticEnergy (0 : NSVelocityField)
  globalClause :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      concreteNSZeroProblemData
  coordinateEnergyIdentity :
    ∀ t,
      Integrable (kineticEnergyDensity (0 : NSVelocityField) t)
        (volume : Measure NSSpace) ∧
        HasDerivAt (normalizedKineticEnergy (0 : NSVelocityField))
          (-(coordinateEnergyDissipationRate (0 : NSVelocityField) 1 t)) t

/-- Committed non-vacuous canary for the actual concrete PDE surface. -/
def concreteNSZeroCanary : ConcreteNSZeroCanary where
  finiteInitialEnergy := concreteNSZero_finiteInitialEnergy
  momentumEquation := concreteNSZero_momentumEquation
  incompressible := concreteNSZero_incompressible
  initialCondition := concreteNSZero_initialCondition
  boundedEnergy := concreteNSZero_boundedEnergy
  globalClause := concreteNSZero_globalRegularityClause
  coordinateEnergyIdentity := concreteNSZero_coordinateEnergyIdentity

/-- Momentum terms in the standard NS scaling all carry exponent `3`. -/
inductive ConcreteNSMomentumTerm where
  | timeDerivative
  | convection
  | pressureGradient
  | viscosityLaplacian
deriving DecidableEq, Repr

/-- Standard scaling exponent under
`uλ(t,x)=λ u(λ²t,λx)`, `pλ(t,x)=λ² p(λ²t,λx)`. -/
def ConcreteNSMomentumTerm.scalingExponent :
    ConcreteNSMomentumTerm → Nat
  | .timeDerivative => 3
  | .convection => 3
  | .pressureGradient => 3
  | .viscosityLaplacian => 3

theorem concreteNS_momentumScalingUniform
    (term : ConcreteNSMomentumTerm) :
    term.scalingExponent = 3 := by
  cases term <;> rfl

/-- Power exponent for the integral of `|uλ|^p` in three dimensions. -/
def velocityLpPowerScalingExponent (p : ℤ) : ℤ :=
  p - 3

theorem concreteNS_L2_power_supercritical :
    velocityLpPowerScalingExponent 2 = -1 := by
  norm_num [velocityLpPowerScalingExponent]

theorem concreteNS_L3_power_critical :
    velocityLpPowerScalingExponent 3 = 0 := by
  norm_num [velocityLpPowerScalingExponent]

theorem concreteNS_L4_power_subcritical :
    velocityLpPowerScalingExponent 4 = 1 := by
  norm_num [velocityLpPowerScalingExponent]

/-- DE-grounded status packet: the zero solution is real, while finite-energy
`L²` scaling alone is supercritical and cannot be promoted as a critical
regularity route. -/
theorem concreteNSZeroCanary_and_scaling_packet :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        concreteNSZeroProblemData ∧
      (∀ term : ConcreteNSMomentumTerm, term.scalingExponent = 3) ∧
      velocityLpPowerScalingExponent 2 = -1 ∧
      velocityLpPowerScalingExponent 3 = 0 ∧
      velocityLpPowerScalingExponent 4 = 1 := by
  exact
    ⟨concreteNSZeroCanary.globalClause,
      concreteNS_momentumScalingUniform,
      concreteNS_L2_power_supercritical,
      concreteNS_L3_power_critical,
      concreteNS_L4_power_subcritical⟩

end ConcreteDEGrounding

end NavierStokes
end FluidDynamics
end Mettapedia
