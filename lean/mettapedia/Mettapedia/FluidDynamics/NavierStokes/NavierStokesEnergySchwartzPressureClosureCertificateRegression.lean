import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzPressureClosureCertificate

/-!
# Regression checks for pressure-closure obstruction certificates
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff Laplacian LineDeriv RealInnerProductSpace SchwartzMap Topology

namespace Regression

theorem pressure_closure_certificate_no_smooth_pressure_regression
    {ν : ℝ} {u : NSVelocityField}
    (C : PressureClosureObstructionCertificate ν u) :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ t x,
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x :=
  C.noSmoothPressure_momentumEquation

theorem pressure_closure_certificate_no_momentum_kernel_regression
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField}
    (C : PressureClosureObstructionCertificate ν u) :
    ¬ SchwartzMomentumClosureKernel ν u p :=
  C.incompatible_momentumClosureKernel

theorem localized_nilpotent_pressure_closure_certificate_regression :
    Nonempty (PressureClosureObstructionCertificate 0 localizedNilpotentStreamVelocityField) :=
  ⟨localizedNilpotentStreamPressureClosureObstructionCertificate⟩

theorem localized_nilpotent_pressure_closure_packet_regression :
    (¬ ∃ p : NSPressureField,
      SchwartzMomentumClosureKernel 0 localizedNilpotentStreamVelocityField p) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution 0,
        S.velocity = localizedNilpotentStreamVelocityField) := by
  exact
    ⟨not_exists_localizedNilpotentStream_momentumClosureKernel,
      not_exists_nonzeroSchwartzConcreteSolution_velocity_localizedNilpotentStream_of_pressureClosureCertificate⟩

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
