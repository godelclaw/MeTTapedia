import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPeriodizationLocalExistencePrerequisites
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityZeroWitness

/-!
# Concrete Navier-Stokes Witness Construction

This file keeps the witness-construction surface honest.  It records the
direct zero-data global witness, and it classifies the boxed steady seed route:
the seed becomes a finite-time witness exactly when the stationary momentum
balance is supplied on the slab.  Thus the boxed seed is not a local existence
theorem for general data; the missing step is an evolved solution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff

section ConcreteWitnessConstruction

/-- The zero velocity and zero pressure fields form an actual global witness
for the fully concrete Navier-Stokes record at zero initial data. -/
def zeroNavierStokesGlobalRegularityWitness
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesGlobalRegularityWitness
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := (0 : NSInitialVelocity)
        smooth_initial := smoothInitialVelocityData_zero
        divergence_free_initial := by
          intro x
          simpa using (initialSpatialDivergence_zero x) } where
  velocity := 0
  pressure := 0
  smooth_velocity := by
    simpa [mkFullyConcreteNavierStokesSurface] using smoothSpaceTimeVelocity_zero
  smooth_pressure := by
    simpa [mkFullyConcreteNavierStokesSurface] using smoothSpaceTimePressure_zero
  momentum_equation := by
    intro t x
    exact momentumEquation_zeroVelocityField_zeroPressure ν t x
  incompressible := by
    intro t x
    simpa [mkFullyConcreteNavierStokesSurface] using (spatialDivergence_zero t x)
  initial_condition := by
    intro x
    rfl
  bounded_energy := by
    refine ⟨0, le_rfl, ?_⟩
    intro t
    constructor
    · have hk :
        kineticEnergyDensity (0 : NSVelocityField) t =
          (fun _ : NSSpace => (0 : ℝ)) := by
        funext x
        simp [kineticEnergyDensity]
      rw [hk]
      exact
        MeasureTheory.integrable_zero NSSpace ℝ
          (MeasureTheory.volume : MeasureTheory.Measure NSSpace)
    · have hE0 : kineticEnergyAt (0 : NSVelocityField) t = 0 := by
        simp [kineticEnergyAt, kineticEnergyDensity]
      simp [hE0]

/-- The direct zero global witness inhabits the structured fully concrete
global-regularity clause. -/
theorem zeroNavierStokesGlobalRegularityWitness_nonempty
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := (0 : NSInitialVelocity)
        smooth_initial := smoothInitialVelocityData_zero
        divergence_free_initial := by
          intro x
          simpa using (initialSpatialDivergence_zero x) } := by
  exact ⟨zeroNavierStokesGlobalRegularityWitness hν⟩

end ConcreteWitnessConstruction

end NavierStokes
end FluidDynamics
end Mettapedia
