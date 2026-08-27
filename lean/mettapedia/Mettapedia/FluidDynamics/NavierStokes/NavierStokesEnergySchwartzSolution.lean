import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyInequality
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationKitIff

/-!
# Energy Identity for Slice-Schwartz Concrete Navier-Stokes Solutions

This module packages the existing Schwartz integration-by-parts lemmas into a
general theorem over an arbitrary concrete Navier-Stokes solution.  The theorem
uses the actual `R^3` momentum equation, incompressibility, pressure gradient,
convection, and Laplacian operators from `mkFullyConcreteNavierStokesSurface`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- A concrete smooth Navier-Stokes solution whose velocity and pressure have
Schwartz spatial slices and whose kinetic energy permits differentiation under
the spatial integral.

The fields are concrete witnesses: the PDE is stated with
`mkFullyConcreteNavierStokesSurface`, and the slice assumptions are given by
actual Schwartz maps equal to the velocity and pressure slices. -/
structure SchwartzConcreteNavierStokesSolution (ν : ℝ) where
  velocity : NSVelocityField
  pressure : NSPressureField
  smooth_velocity : smoothSpaceTimeVelocity velocity
  smooth_pressure : smoothSpaceTimePressure pressure
  momentum_equation : SatisfiesMomentumEquation mkFullyConcreteNavierStokesSurface ν velocity pressure
  incompressible : IsIncompressible mkFullyConcreteNavierStokesSurface velocity
  bounded_energy : boundedKineticEnergy velocity
  velocitySlice : NSTime → 𝓢(NSSpace, NSSpace)
  velocitySlice_eq : ∀ t x, velocity t x = velocitySlice t x
  pressureSlice : NSTime → 𝓢(NSSpace, ℝ)
  pressureSlice_eq : ∀ t x, pressure t x = pressureSlice t x
  energy_derivative : EnergyDerivativeFormula velocity

namespace SchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν)

/-- The packaged solution exposes the literal concrete momentum equation. -/
theorem momentumEquation_explicit :
    ∀ t x,
      timeVelocityDerivative S.velocity t x + spatialConvection S.velocity t x +
          spatialPressureGradient S.pressure t x =
        ν • spatialLaplacian S.velocity t x :=
  satisfiesMomentumEquation_mkFullyConcreteNavierStokesSurface_iff.mp S.momentum_equation

/-- The packaged incompressibility hypothesis is literal spatial-divergence
vanishing on `R^3`. -/
theorem spatialDivergence_zero :
    ∀ t x, spatialDivergence S.velocity t x = 0 :=
  isIncompressible_mkFullyConcreteNavierStokesSurface_iff.mp S.incompressible

/-- The velocity and pressure pairings needed in the energy calculation are
integrable on every time slice. -/
theorem energyPairingIntegrable :
    EnergyPairingIntegrable S.velocity S.pressure := by
  intro t
  refine ⟨?_, ?_, ?_⟩
  · exact
      integrable_laplacianEnergyPairing_of_schwartzSlice
        (u := S.velocity)
        (t := t)
        (f := S.velocitySlice t)
        (hslice := S.velocitySlice_eq t)
  · exact
      integrable_convectionEnergyPairing_of_schwartzSlice
        (u := S.velocity)
        (t := t)
        (f := S.velocitySlice t)
        (hslice := S.velocitySlice_eq t)
  · have hp :
        S.pressure = fun s : NSTime => fun x : NSSpace => S.pressureSlice s x := by
      funext s x
      exact S.pressureSlice_eq s x
    rw [hp]
    exact
      integrable_pressureEnergyPairing_of_schwartzSlice_schwartzPressureSlice
        (u := S.velocity)
        (t := t)
        (f := S.velocitySlice t)
        (q := S.pressureSlice)
        (hslice := S.velocitySlice_eq t)

/-- The nonlinear transport term contributes no work to the global energy
balance.  This is the incompressibility cancellation
`integral u . (u . grad)u = 0`, proved from the slice-Schwartz integration by
parts lemma. -/
theorem convectionEnergyCancellation :
    ∀ t, ∫ x, convectionEnergyPairing S.velocity t x ∂volume = 0 := by
  intro t
  exact
    integral_convectionEnergyPairing_of_schwartzSlice_of_spatialDivergence_zero
      (u := S.velocity)
      (t := t)
      (f := S.velocitySlice t)
      (hslice := S.velocitySlice_eq t)
      (hdiv := fun x => S.spatialDivergence_zero t x)

/-- The pressure term contributes no work to the global energy balance.  This is
the incompressibility cancellation `integral u . grad p = 0`, proved by
coordinatewise integration by parts for arbitrary Schwartz pressure slices. -/
theorem pressureEnergyCancellation :
    ∀ t, ∫ x, pressureEnergyPairing S.velocity S.pressure t x ∂volume = 0 := by
  intro t
  have hp :
      S.pressure = fun s : NSTime => fun x : NSSpace => S.pressureSlice s x := by
    funext s x
    exact S.pressureSlice_eq s x
  rw [hp]
  exact
    integral_pressureEnergyPairing_of_schwartzSlice_schwartzPressureSlice_of_spatialDivergence_zero
      (u := S.velocity)
      (t := t)
      (f := S.velocitySlice t)
      (q := S.pressureSlice)
      (hslice := S.velocitySlice_eq t)
      (hdiv := fun x => S.spatialDivergence_zero t x)

/-- The viscous Laplacian contributes the negative coordinatewise dissipation
by the Schwartz integration-by-parts identity
`integral u . Delta u = - integral sum_i |partial_i u|^2`. -/
theorem coordinateViscousEnergyPairingFormula :
    CoordinateViscousEnergyPairingFormula S.velocity := by
  intro t
  exact
    coordinateViscousEnergyPairingFormula_of_schwartzSlice
      (u := S.velocity)
      (t := t)
      (f := S.velocitySlice t)
      (hslice := S.velocitySlice_eq t)

/-- General coordinate energy dissipation identity for an arbitrary
slice-Schwartz solution of the fully concrete three-dimensional
Navier-Stokes equation. -/
theorem coordinateEnergyDissipationIdentity :
    ∀ t,
      HasDerivAt (normalizedKineticEnergy S.velocity)
        (-(coordinateEnergyDissipationRate S.velocity ν t)) t :=
  coordinateEnergyDissipationIdentity_smooth
    (u := S.velocity)
    (p := S.pressure)
    (ν := ν)
    S.energy_derivative
    S.momentumEquation_explicit
    S.energyPairingIntegrable
    S.coordinateViscousEnergyPairingFormula
    S.pressureEnergyCancellation
    S.convectionEnergyCancellation

/-- Meaningful guarded form: every time slice has integrable kinetic energy,
and the same coordinate energy dissipation identity holds there. -/
theorem meaningfulCoordinateEnergyDissipationIdentity :
    ∀ t,
      Integrable (kineticEnergyDensity S.velocity t) ∧
        HasDerivAt (normalizedKineticEnergy S.velocity)
          (-(coordinateEnergyDissipationRate S.velocity ν t)) t :=
  meaningfulCoordinateEnergyDissipationIdentity_smooth_of_boundedKineticEnergy
    (u := S.velocity)
    (p := S.pressure)
    (ν := ν)
    S.bounded_energy
    S.energy_derivative
    S.momentumEquation_explicit
    S.energyPairingIntegrable
    S.coordinateViscousEnergyPairingFormula
    S.pressureEnergyCancellation
    S.convectionEnergyCancellation

/-- Nonnegative viscosity turns the exact identity into monotone kinetic-energy
decay for every solution in this concrete Schwartz class. -/
theorem normalizedKineticEnergy_antitone (hν : 0 ≤ ν) :
    Antitone (normalizedKineticEnergy S.velocity) :=
  coordinateEnergyDissipationIdentity_smooth_antitone_normalizedKineticEnergy
    (u := S.velocity)
    (p := S.pressure)
    (ν := ν)
    hν
    S.energy_derivative
    S.momentumEquation_explicit
    S.energyPairingIntegrable
    S.coordinateViscousEnergyPairingFormula
    S.pressureEnergyCancellation
    S.convectionEnergyCancellation

/-- Two-time kinetic-energy inequality extracted from the exact identity. -/
theorem kineticEnergyAt_le_of_le (hν : 0 ≤ ν) {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    kineticEnergyAt S.velocity t₁ ≤ kineticEnergyAt S.velocity t₀ :=
  coordinateEnergyDissipationIdentity_smooth_kineticEnergyAt_le_of_le
    (u := S.velocity)
    (p := S.pressure)
    (ν := ν)
    hν
    S.energy_derivative
    S.momentumEquation_explicit
    S.energyPairingIntegrable
    S.coordinateViscousEnergyPairingFormula
    S.pressureEnergyCancellation
    S.convectionEnergyCancellation
    ht

/-- Compact packet for the nontrivial energy node: both real cancellations, the
viscous Laplacian identity, and the final dissipation identity. -/
theorem cancellation_and_coordinateEnergyDissipation_packet :
    (∀ t, ∫ x, pressureEnergyPairing S.velocity S.pressure t x ∂volume = 0) ∧
      (∀ t, ∫ x, convectionEnergyPairing S.velocity t x ∂volume = 0) ∧
      CoordinateViscousEnergyPairingFormula S.velocity ∧
      ∀ t,
        HasDerivAt (normalizedKineticEnergy S.velocity)
          (-(coordinateEnergyDissipationRate S.velocity ν t)) t :=
  ⟨S.pressureEnergyCancellation,
    S.convectionEnergyCancellation,
    S.coordinateViscousEnergyPairingFormula,
    S.coordinateEnergyDissipationIdentity⟩

end SchwartzConcreteNavierStokesSolution

/-- Explicit universal form of the slice-Schwartz concrete Navier-Stokes energy
identity.  For any smooth bounded-energy velocity/pressure pair solving the
fully concrete `R^3` equation, with Schwartz velocity and pressure slices and
the standard derivative-under-the-integral energy admissibility, the pressure
and convection work terms cancel, the viscous term is the negative
coordinatewise dissipation, and the normalized kinetic energy has derivative
`-nu * integral sum_i |partial_i u|^2`. -/
theorem coordinateEnergyDissipationIdentity_of_schwartzConcreteSolution
    (ν : ℝ) (u : NSVelocityField) (p : NSPressureField)
    (hsmooth_u : smoothSpaceTimeVelocity u)
    (hsmooth_p : smoothSpaceTimePressure p)
    (hmomentum : SatisfiesMomentumEquation mkFullyConcreteNavierStokesSurface ν u p)
    (hincompressible : IsIncompressible mkFullyConcreteNavierStokesSurface u)
    (hbounded : boundedKineticEnergy u)
    (velocitySlice : NSTime → 𝓢(NSSpace, NSSpace))
    (hvelocitySlice : ∀ t x, u t x = velocitySlice t x)
    (pressureSlice : NSTime → 𝓢(NSSpace, ℝ))
    (hpressureSlice : ∀ t x, p t x = pressureSlice t x)
    (hderiv : EnergyDerivativeFormula u) :
    (∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0) ∧
      (∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0) ∧
      CoordinateViscousEnergyPairingFormula u ∧
      ∀ t,
        HasDerivAt (normalizedKineticEnergy u)
          (-(coordinateEnergyDissipationRate u ν t)) t := by
  let S : SchwartzConcreteNavierStokesSolution ν := {
    velocity := u
    pressure := p
    smooth_velocity := hsmooth_u
    smooth_pressure := hsmooth_p
    momentum_equation := hmomentum
    incompressible := hincompressible
    bounded_energy := hbounded
    velocitySlice := velocitySlice
    velocitySlice_eq := hvelocitySlice
    pressureSlice := pressureSlice
    pressureSlice_eq := hpressureSlice
    energy_derivative := hderiv
  }
  exact S.cancellation_and_coordinateEnergyDissipation_packet

/-- Direct energy-inequality corollary for any nonnegative-viscosity
slice-Schwartz concrete solution satisfying the same hypotheses as the exact
identity theorem. -/
theorem kineticEnergyAt_le_of_le_of_schwartzConcreteSolution
    {ν : ℝ} (hν : 0 ≤ ν) (u : NSVelocityField) (p : NSPressureField)
    (hsmooth_u : smoothSpaceTimeVelocity u)
    (hsmooth_p : smoothSpaceTimePressure p)
    (hmomentum : SatisfiesMomentumEquation mkFullyConcreteNavierStokesSurface ν u p)
    (hincompressible : IsIncompressible mkFullyConcreteNavierStokesSurface u)
    (hbounded : boundedKineticEnergy u)
    (velocitySlice : NSTime → 𝓢(NSSpace, NSSpace))
    (hvelocitySlice : ∀ t x, u t x = velocitySlice t x)
    (pressureSlice : NSTime → 𝓢(NSSpace, ℝ))
    (hpressureSlice : ∀ t x, p t x = pressureSlice t x)
    (hderiv : EnergyDerivativeFormula u)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    kineticEnergyAt u t₁ ≤ kineticEnergyAt u t₀ := by
  let S : SchwartzConcreteNavierStokesSolution ν := {
    velocity := u
    pressure := p
    smooth_velocity := hsmooth_u
    smooth_pressure := hsmooth_p
    momentum_equation := hmomentum
    incompressible := hincompressible
    bounded_energy := hbounded
    velocitySlice := velocitySlice
    velocitySlice_eq := hvelocitySlice
    pressureSlice := pressureSlice
    pressureSlice_eq := hpressureSlice
    energy_derivative := hderiv
  }
  exact S.kineticEnergyAt_le_of_le hν ht

end NavierStokes
end FluidDynamics
end Mettapedia
