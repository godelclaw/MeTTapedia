import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolutionObstruction

/-!
# Slice-Schwartz Stokes-Flow Kernel

This module isolates the exact Stokes-flow subroute inside the concrete
slice-Schwartz Navier-Stokes interface.  If the nonlinear convection and
pressure-gradient terms vanish pointwise, the momentum equation reduces to the
heat/Stokes equation `partial_t u = nu Delta u`.  Any nonzero positive-viscosity
inhabitant of that subroute still carries the strict energy-dissipation and
non-recurrence consequences of the universal energy identity.

This is a reusable constraint packet for future canary searches.  It does not
construct a positive-viscosity nonzero slice-Schwartz solution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap Topology

/-- Reusable kernel for the exact Stokes-flow subroute inside the concrete
slice-Schwartz solution interface. -/
structure SchwartzStokesFlowKernel
    (ν : ℝ) (u : NSVelocityField) (p : NSPressureField) where
  concrete : SchwartzConcreteSolutionKernel ν u p
  zeroConvection : ∀ t x, spatialConvection u t x = 0
  zeroPressureGradient : ∀ t x, spatialPressureGradient p t x = 0
  stokesEquation :
    ∀ t x, timeVelocityDerivative u t x = ν • spatialLaplacian u t x

/-- Nonzero refinement of the exact Stokes-flow subroute. -/
structure NonzeroSchwartzStokesFlowKernel
    (ν : ℝ) (u : NSVelocityField) (p : NSPressureField)
    extends SchwartzStokesFlowKernel ν u p where
  nonzero_velocity : ∃ t x, u t x ≠ 0

namespace SchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν)

/-- A slice-Schwartz concrete solution with vanishing convection and pressure
gradient is an exact Stokes/heat-flow solution. -/
def stokesFlowKernel
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0) :
    SchwartzStokesFlowKernel ν S.velocity S.pressure where
  concrete := S.concreteSolutionKernel
  zeroConvection := hconv
  zeroPressureGradient := hpressure
  stokesEquation := by
    intro t x
    have h := S.momentumEquation_explicit t x
    rw [hconv t x, hpressure t x] at h
    simpa using h

/-- Compact Stokes-flow packet: exact heat/Stokes equation plus the inherited
energy kernel. -/
theorem stokesFlowKernel_and_energyIdentityKernel
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0) :
    SchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      SchwartzEnergyIdentityKernel ν S.velocity S.pressure :=
  ⟨S.stokesFlowKernel hconv hpressure, S.energyIdentityKernel⟩

end SchwartzConcreteNavierStokesSolution

namespace NonzeroSchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)

/-- Nonzero solutions with vanishing convection and pressure gradient inherit
the exact Stokes-flow kernel. -/
def nonzeroStokesFlowKernel
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure where
  toSchwartzStokesFlowKernel :=
    S.toSchwartzConcreteNavierStokesSolution.stokesFlowKernel hconv hpressure
  nonzero_velocity := S.nonzero_velocity

/-- Positive-viscosity nonzero Stokes-flow candidates must exhibit strict
energy dissipation at some time. -/
theorem stokesFlow_strictDissipation_packet
    (hν : 0 < ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      ∃ t : NSTime,
        0 < coordinateEnergyDissipationRate S.velocity ν t ∧
          HasDerivAt (normalizedKineticEnergy S.velocity)
            (-(coordinateEnergyDissipationRate S.velocity ν t)) t ∧
          -(coordinateEnergyDissipationRate S.velocity ν t) < 0 :=
  ⟨S.nonzeroStokesFlowKernel hconv hpressure,
    S.exists_strict_coordinateEnergyDissipationIdentity_of_pos_viscosity hν⟩

/-- Positive-viscosity nonzero Stokes-flow candidates cannot be periodic in
velocity with a positive period. -/
theorem stokesFlow_not_forall_velocity_periodic_of_pos_viscosity
    (hν : 0 < ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {P : NSTime} (hP : 0 < P) :
    ¬ ∀ t : NSTime, ∀ x : NSSpace,
      S.velocity (t + P) x = S.velocity t x := by
  have _kernel : NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure :=
    S.nonzeroStokesFlowKernel hconv hpressure
  intro hperiod
  exact S.not_forall_velocity_periodic_of_pos_viscosity hν hP hperiod

end NonzeroSchwartzConcreteNavierStokesSolution

/-- Global no-go for recurrent exact Stokes-flow canary shortcuts: a
positive-viscosity nonzero slice-Schwartz solution with zero convection and
zero pressure gradient cannot have positive-period velocity recurrence. -/
theorem not_exists_nonzeroSchwartzStokesFlow_velocity_periodic_of_pos_viscosity
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      (∀ t x, spatialConvection S.velocity t x = 0) ∧
        (∀ t x, spatialPressureGradient S.pressure t x = 0) ∧
        ∃ P : NSTime,
          0 < P ∧
            ∀ t : NSTime, ∀ x : NSSpace,
              S.velocity (t + P) x = S.velocity t x := by
  rintro ⟨S, hconv, hpressure, P, hP, hperiod⟩
  exact
    S.stokesFlow_not_forall_velocity_periodic_of_pos_viscosity
      hν hconv hpressure hP hperiod

end NavierStokes
end FluidDynamics
end Mettapedia
