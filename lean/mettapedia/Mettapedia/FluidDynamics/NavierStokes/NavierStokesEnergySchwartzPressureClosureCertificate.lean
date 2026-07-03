import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzLocalizedNilpotentStreamObstruction

/-!
# Slice-Schwartz Pressure-Closure Certificates

This module packages the residual-curl obstruction as a generator-facing
certificate.  A candidate velocity whose pressure residual
`nu Delta u - partial_t u - (u.grad)u` has nonzero curl at one point cannot be
closed by any smooth pressure slice, and therefore cannot inhabit the ordinary
or nonzero slice-Schwartz concrete solution interfaces.

The localized nilpotent stream supplies an explicit nonzero divergence-free
Schwartz seed where this certificate fires.  This is a failed-canary boundary,
not a positive-viscosity nonzero solution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff Laplacian LineDeriv RealInnerProductSpace SchwartzMap Topology

/-- A compact pressure-closure obstruction certificate for a candidate
velocity.  Candidate generators should try to produce this object as soon as a
residual-curl failure is found; any positive canary must prove no such
certificate exists for its velocity. -/
structure PressureClosureObstructionCertificate
    (ν : ℝ) (u : NSVelocityField) where
  time : NSTime
  point : NSSpace
  residualVorticity_ne_zero :
    spatialVorticity (momentumPressureResidual ν u) time point ≠ 0

namespace PressureClosureObstructionCertificate

variable {ν : ℝ} {u : NSVelocityField}
/-- Recover the existential residual-curl witness used by the older
pressure-obstruction theorem. -/
theorem residualVorticity_witness
    (C : PressureClosureObstructionCertificate ν u) :
    ∃ t : NSTime, ∃ x : NSSpace,
      spatialVorticity (momentumPressureResidual ν u) t x ≠ 0 :=
  ⟨C.time, C.point, C.residualVorticity_ne_zero⟩

/-- A residual-curl certificate rules out every smooth-pressure closure of the
literal momentum equation for the candidate velocity. -/
theorem noSmoothPressure_momentumEquation
    (C : PressureClosureObstructionCertificate ν u) :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ t x,
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x :=
  not_exists_smoothPressure_momentumEquation_of_momentumPressureResidual_vorticity_ne_zero
    C.residualVorticity_witness

/-- The certificate is incompatible with a reusable momentum-closure kernel. -/
theorem incompatible_momentumClosureKernel
    (C : PressureClosureObstructionCertificate ν u) {p : NSPressureField} :
    ¬ SchwartzMomentumClosureKernel ν u p := by
  intro K
  exact C.residualVorticity_ne_zero
    (K.pressureResidual_vorticity_zero C.time C.point)

/-- The certificate is incompatible with a full concrete-solution kernel. -/
theorem incompatible_concreteSolutionKernel
    (C : PressureClosureObstructionCertificate ν u) {p : NSPressureField} :
    ¬ SchwartzConcreteSolutionKernel ν u p := by
  intro K
  exact C.incompatible_momentumClosureKernel K.momentum

/-- A residual-curl certificate rules out ordinary slice-Schwartz concrete
solutions with this velocity field. -/
theorem noSchwartzConcreteSolution_velocity
    (C : PressureClosureObstructionCertificate ν u) :
    ¬ ∃ S : SchwartzConcreteNavierStokesSolution ν, S.velocity = u :=
  not_exists_schwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero
    C.residualVorticity_witness

/-- A residual-curl certificate also rules out nonzero slice-Schwartz concrete
solutions with this velocity field. -/
theorem noNonzeroSchwartzConcreteSolution_velocity
    (C : PressureClosureObstructionCertificate ν u) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν, S.velocity = u :=
  not_exists_nonzeroSchwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero
    C.residualVorticity_witness

end PressureClosureObstructionCertificate

/-- The localized nilpotent stream gives an explicit pressure-closure
obstruction certificate at viscosity `0`. -/
def localizedNilpotentStreamPressureClosureObstructionCertificate :
    PressureClosureObstructionCertificate 0 localizedNilpotentStreamVelocityField where
  time := 0
  point := 0
  residualVorticity_ne_zero :=
    spatialVorticity_momentumPressureResidual_zero_localizedNilpotentStreamVelocityField_origin_ne_zero

/-- The concrete localized nilpotent stream certificate blocks smooth-pressure
closure of the stationary inviscid candidate. -/
theorem localizedNilpotentStreamPressureClosureObstructionCertificate_noSmoothPressure :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ t x,
          timeVelocityDerivative localizedNilpotentStreamVelocityField t x +
              spatialConvection localizedNilpotentStreamVelocityField t x +
              spatialPressureGradient p t x =
            (0 : ℝ) • spatialLaplacian localizedNilpotentStreamVelocityField t x :=
  localizedNilpotentStreamPressureClosureObstructionCertificate.noSmoothPressure_momentumEquation

/-- The concrete localized nilpotent stream certificate blocks reusable
momentum-closure kernels for that velocity. -/
theorem not_exists_localizedNilpotentStream_momentumClosureKernel :
    ¬ ∃ p : NSPressureField,
      SchwartzMomentumClosureKernel 0 localizedNilpotentStreamVelocityField p := by
  rintro ⟨p, K⟩
  exact
    localizedNilpotentStreamPressureClosureObstructionCertificate
      |>.incompatible_momentumClosureKernel K

/-- The concrete localized nilpotent stream certificate blocks reusable full
solution kernels for that velocity. -/
theorem not_exists_localizedNilpotentStream_concreteSolutionKernel :
    ¬ ∃ p : NSPressureField,
      SchwartzConcreteSolutionKernel 0 localizedNilpotentStreamVelocityField p := by
  rintro ⟨p, K⟩
  exact
    localizedNilpotentStreamPressureClosureObstructionCertificate
      |>.incompatible_concreteSolutionKernel K

/-- The concrete localized nilpotent stream certificate blocks ordinary
slice-Schwartz concrete solutions with that velocity. -/
theorem not_exists_schwartzConcreteSolution_velocity_localizedNilpotentStream_of_pressureClosureCertificate :
    ¬ ∃ S : SchwartzConcreteNavierStokesSolution 0,
      S.velocity = localizedNilpotentStreamVelocityField :=
  localizedNilpotentStreamPressureClosureObstructionCertificate.noSchwartzConcreteSolution_velocity

/-- The concrete localized nilpotent stream certificate blocks nonzero
slice-Schwartz concrete solutions with that velocity. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_velocity_localizedNilpotentStream_of_pressureClosureCertificate :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution 0,
      S.velocity = localizedNilpotentStreamVelocityField :=
  localizedNilpotentStreamPressureClosureObstructionCertificate.noNonzeroSchwartzConcreteSolution_velocity

/-- Generator-facing packet for the explicit localized nilpotent stream:
nonzero divergence-free Schwartz data exist, but this stationary inviscid
velocity has a residual-curl certificate and therefore cannot be closed by
smooth pressure or by the slice-Schwartz solution kernels. -/
theorem localizedNilpotentStream_pressureClosureCertificate_packet :
    (∃ u₀ : NSSchwartzDivergenceFreeInitialVelocity,
      ∃ x : NSSpace, u₀.1 x ≠ 0) ∧
      Nonempty (PressureClosureObstructionCertificate 0 localizedNilpotentStreamVelocityField) ∧
      (¬ ∃ p : NSPressureField,
        smoothSpaceTimePressure p ∧
          ∀ t x,
            timeVelocityDerivative localizedNilpotentStreamVelocityField t x +
                spatialConvection localizedNilpotentStreamVelocityField t x +
                spatialPressureGradient p t x =
              (0 : ℝ) • spatialLaplacian localizedNilpotentStreamVelocityField t x) ∧
      (¬ ∃ p : NSPressureField,
        SchwartzMomentumClosureKernel 0 localizedNilpotentStreamVelocityField p) ∧
      (¬ ∃ p : NSPressureField,
        SchwartzConcreteSolutionKernel 0 localizedNilpotentStreamVelocityField p) ∧
      (¬ ∃ S : SchwartzConcreteNavierStokesSolution 0,
        S.velocity = localizedNilpotentStreamVelocityField) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution 0,
        S.velocity = localizedNilpotentStreamVelocityField) := by
  exact
    ⟨⟨nsLocalizedNilpotentStreamDivergenceFreeInitialVelocity,
        nsLocalizedNilpotentStreamDivergenceFreeInitialVelocity_nonzero⟩,
      ⟨localizedNilpotentStreamPressureClosureObstructionCertificate⟩,
      localizedNilpotentStreamPressureClosureObstructionCertificate_noSmoothPressure,
      not_exists_localizedNilpotentStream_momentumClosureKernel,
      not_exists_localizedNilpotentStream_concreteSolutionKernel,
      not_exists_schwartzConcreteSolution_velocity_localizedNilpotentStream_of_pressureClosureCertificate,
      not_exists_nonzeroSchwartzConcreteSolution_velocity_localizedNilpotentStream_of_pressureClosureCertificate⟩

end NavierStokes
end FluidDynamics
end Mettapedia
