import Mettapedia.FluidDynamics.NavierStokes.NavierStokesDEGroundedCanary

/-!
# Regression checks for the DE-grounded Navier-Stokes canary

These checks keep the concrete zero-solution canary and scaling arithmetic
visible to the Navier-Stokes regression umbrella.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

theorem concreteNSZero_globalRegularityClause_regression :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      concreteNSZeroProblemData := by
  exact concreteNSZero_globalRegularityClause

theorem concreteNSZero_coordinateEnergyIdentity_regression :
    ∀ t,
      MeasureTheory.Integrable
        (kineticEnergyDensity (0 : NSVelocityField) t)
        (MeasureTheory.volume : MeasureTheory.Measure NSSpace) ∧
        HasDerivAt (normalizedKineticEnergy (0 : NSVelocityField))
          (-(coordinateEnergyDissipationRate (0 : NSVelocityField) 1 t)) t := by
  exact concreteNSZero_coordinateEnergyIdentity

theorem concreteNSZeroCanary_and_scaling_packet_regression :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        concreteNSZeroProblemData ∧
      (∀ term : ConcreteNSMomentumTerm, term.scalingExponent = 3) ∧
      velocityLpPowerScalingExponent 2 = -1 ∧
      velocityLpPowerScalingExponent 3 = 0 ∧
      velocityLpPowerScalingExponent 4 = 1 := by
  exact concreteNSZeroCanary_and_scaling_packet

end NavierStokes
end FluidDynamics
end Mettapedia
