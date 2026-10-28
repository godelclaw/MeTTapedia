import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyMeaningfulSchwartzCore
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyMeaningfulSchwartzPressures
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyMeaningfulSchwartzAffineScalar
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyMeaningfulSchwartzInequalities
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyMeaningfulSchwartzDivergenceFree

/-!
# Navier-Stokes Energy: Zero

Zero-solution energy, dissipation, integrability, and coordinate energy identity checks.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- The zero field has zero normalized kinetic energy on every time slice. -/
theorem normalizedKineticEnergy_zero :
    normalizedKineticEnergy (0 : NSVelocityField) = fun _ : NSTime => 0 := by
  funext t
  simp [normalizedKineticEnergy, kineticEnergyAt, kineticEnergyDensity]

/-- The zero field has zero enstrophy density on every time slice. -/
theorem enstrophyDensity_zero (t : NSTime) :
    enstrophyDensity (0 : NSVelocityField) t = fun _ : NSSpace => 0 := by
  funext x
  rw [enstrophyDensity]
  simp [spatialFDeriv_zero]

/-- The zero field has zero total enstrophy on every time slice. -/
theorem enstrophyAt_zero :
    enstrophyAt (0 : NSVelocityField) = fun _ : NSTime => 0 := by
  funext t
  rw [enstrophyAt, enstrophyDensity_zero]
  simp

/-- The zero field has zero coordinatewise enstrophy density on every time
slice. -/
theorem coordinateEnstrophyDensity_zero (t : NSTime) :
    coordinateEnstrophyDensity (0 : NSVelocityField) t = fun _ : NSSpace => 0 := by
  funext x
  simp [coordinateEnstrophyDensity, spatialFDeriv_zero]

/-- The zero field has zero total coordinatewise enstrophy on every time
slice. -/
theorem coordinateEnstrophyAt_zero :
    coordinateEnstrophyAt (0 : NSVelocityField) = fun _ : NSTime => 0 := by
  funext t
  rw [coordinateEnstrophyAt, coordinateEnstrophyDensity_zero]
  simp

/-- The zero field has zero dissipation rate for every viscosity. -/
theorem energyDissipationRate_zero (ν : ℝ) :
    energyDissipationRate (0 : NSVelocityField) ν = fun _ : NSTime => 0 := by
  funext t
  rw [energyDissipationRate, enstrophyAt_zero]
  simp

/-- The zero field has zero corrected dissipation rate for every viscosity. -/
theorem coordinateEnergyDissipationRate_zero (ν : ℝ) :
    coordinateEnergyDissipationRate (0 : NSVelocityField) ν = fun _ : NSTime => 0 := by
  funext t
  rw [coordinateEnergyDissipationRate, coordinateEnstrophyAt_zero]
  simp

/-- The zero field has zero `u · ∂ₜu` pairing. -/
theorem timeEnergyPairing_zero (t : NSTime) :
    timeEnergyPairing (0 : NSVelocityField) t = fun _ : NSSpace => 0 := by
  funext x
  simp [timeEnergyPairing]

/-- The zero field has zero nonlinear energy pairing. -/
theorem convectionEnergyPairing_zero (t : NSTime) :
    convectionEnergyPairing (0 : NSVelocityField) t = fun _ : NSSpace => 0 := by
  funext x
  simp [convectionEnergyPairing]

/-- The zero field has zero pressure pairing against any pressure field. -/
theorem pressureEnergyPairing_zero_left (p : NSPressureField) (t : NSTime) :
    pressureEnergyPairing (0 : NSVelocityField) p t = fun _ : NSSpace => 0 := by
  funext x
  simp [pressureEnergyPairing]

/-- The zero field has zero viscous energy pairing. -/
theorem laplacianEnergyPairing_zero (t : NSTime) :
    laplacianEnergyPairing (0 : NSVelocityField) t = fun _ : NSSpace => 0 := by
  funext x
  have hLaplacian :
      spatialLaplacian (0 : NSVelocityField) t x = 0 := by
    simpa [constantVelocityField] using
      spatialLaplacian_constantVelocityField (0 : NSSpace) t x
  simp [laplacianEnergyPairing, hLaplacian]

/-- The derivative-under-the-integral seam holds on the concrete zero solution. -/
theorem EnergyDerivativeFormula_zero :
    EnergyDerivativeFormula (0 : NSVelocityField) := by
  intro t
  rw [normalizedKineticEnergy_zero]
  have hPairIntegral : ∫ x, timeEnergyPairing (0 : NSVelocityField) t x ∂volume = 0 := by
    rw [timeEnergyPairing_zero]
    simp
  rw [hPairIntegral]
  simpa using (hasDerivAt_const t (0 : ℝ))

/-- The viscous integration-by-parts seam holds trivially on the zero solution.
-/
theorem ViscousEnergyPairingFormula_zero :
    ViscousEnergyPairingFormula (0 : NSVelocityField) := by
  intro t
  rw [laplacianEnergyPairing_zero, enstrophyAt_zero]
  simp

/-- The corrected viscous integration-by-parts seam holds trivially on the zero
solution. -/
theorem CoordinateViscousEnergyPairingFormula_zero :
    CoordinateViscousEnergyPairingFormula (0 : NSVelocityField) := by
  intro t
  rw [laplacianEnergyPairing_zero, coordinateEnstrophyAt_zero]
  simp

/-- All three space pairings are integrable on the zero velocity / zero pressure
baseline. -/
theorem EnergyPairingIntegrable_zero :
    EnergyPairingIntegrable (0 : NSVelocityField) (0 : NSPressureField) := by
  intro t
  constructor
  · rw [laplacianEnergyPairing_zero]
    exact integrable_zero NSSpace ℝ (volume : Measure NSSpace)
  constructor
  · rw [convectionEnergyPairing_zero]
    exact integrable_zero NSSpace ℝ (volume : Measure NSSpace)
  · rw [pressureEnergyPairing_zero_left (0 : NSPressureField)]
    exact integrable_zero NSSpace ℝ (volume : Measure NSSpace)

/-- Concrete baseline: the smooth zero solution satisfies the energy
dissipation identity for every viscosity. This pairs the theorem-level energy
reduction with an actual bottom-up Navier-Stokes solution on `ℝ × ℝ^3`. -/
theorem energyDissipationIdentity_smooth_zero (ν : ℝ) :
    ∀ t,
      HasDerivAt (normalizedKineticEnergy (0 : NSVelocityField))
        (-(energyDissipationRate (0 : NSVelocityField) ν t)) t := by
  exact
    energyDissipationIdentity_smooth
      (u := (0 : NSVelocityField))
      (p := (0 : NSPressureField))
      (ν := ν)
      EnergyDerivativeFormula_zero
      (fun t x => momentumEquation_zeroVelocityField_zeroPressure ν t x)
      EnergyPairingIntegrable_zero
      (by
        intro t
        rw [laplacianEnergyPairing_zero, enstrophyAt_zero]
        simp)
      (by
        intro t
        rw [pressureEnergyPairing_zero_left (0 : NSPressureField)]
        simp)
      (by
        intro t
        rw [convectionEnergyPairing_zero]
        simp)

/-- Concrete corrected baseline: the smooth zero solution satisfies the
coordinatewise energy dissipation identity for every viscosity. -/
theorem coordinateEnergyDissipationIdentity_smooth_zero (ν : ℝ) :
    ∀ t,
      HasDerivAt (normalizedKineticEnergy (0 : NSVelocityField))
        (-(coordinateEnergyDissipationRate (0 : NSVelocityField) ν t)) t := by
  exact
    coordinateEnergyDissipationIdentity_smooth
      (u := (0 : NSVelocityField))
      (p := (0 : NSPressureField))
      (ν := ν)
      EnergyDerivativeFormula_zero
      (fun t x => momentumEquation_zeroVelocityField_zeroPressure ν t x)
      EnergyPairingIntegrable_zero
      CoordinateViscousEnergyPairingFormula_zero
      (by
        intro t
        rw [pressureEnergyPairing_zero_left (0 : NSPressureField)]
        simp)
      (by
        intro t
        rw [convectionEnergyPairing_zero]
        simp)

/-- The zero solution satisfies the repaired bounded-energy guarded coordinate
energy identity. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_zero (ν : ℝ) :
    ∀ t,
      MeasureTheory.Integrable (kineticEnergyDensity (0 : NSVelocityField) t) ∧
        HasDerivAt (normalizedKineticEnergy (0 : NSVelocityField))
          (-(coordinateEnergyDissipationRate (0 : NSVelocityField) ν t)) t := by
  have henergy : boundedKineticEnergy (0 : NSVelocityField) := by
    refine ⟨0, le_rfl, ?_⟩
    intro t
    constructor
    · have hzeroDensity : kineticEnergyDensity (0 : NSVelocityField) t = fun _ : NSSpace => 0 := by
        funext x
        simp [kineticEnergyDensity]
      rw [hzeroDensity]
      exact integrable_zero NSSpace ℝ (volume : Measure NSSpace)
    · simp [kineticEnergyAt, kineticEnergyDensity]
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_boundedKineticEnergy
      (u := (0 : NSVelocityField))
      (p := (0 : NSPressureField))
      (ν := ν)
      henergy
      EnergyDerivativeFormula_zero
      (fun t x => momentumEquation_zeroVelocityField_zeroPressure ν t x)
      EnergyPairingIntegrable_zero
      CoordinateViscousEnergyPairingFormula_zero
      (by
        intro t
        rw [pressureEnergyPairing_zero_left (0 : NSPressureField)]
        simp)
      (by
        intro t
        rw [convectionEnergyPairing_zero]
        simp)
end NavierStokes
end FluidDynamics
end Mettapedia
