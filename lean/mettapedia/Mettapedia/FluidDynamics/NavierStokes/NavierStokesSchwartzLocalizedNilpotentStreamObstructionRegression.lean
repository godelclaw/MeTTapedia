import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzLocalizedNilpotentStreamObstruction

/-!
# Regression checks for localized nilpotent stream obstructions
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff LineDeriv SchwartzMap Topology

namespace Regression

theorem localized_nilpotent_stream_germ_pressure_obstruction_regression
    {u : NSVelocityField} {t : NSTime}
    (hvel : (fun x : NSSpace => u t x) =ᶠ[𝓝 (0 : NSSpace)]
      fun x : NSSpace => localizedNilpotentStreamVelocityField 0 x)
    (htime : (fun x : NSSpace => timeVelocityDerivative u t x) =ᶠ[𝓝 (0 : NSSpace)]
      fun _ : NSSpace => 0) :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ s x,
          timeVelocityDerivative u s x + spatialConvection u s x +
              spatialPressureGradient p s x =
            (0 : ℝ) • spatialLaplacian u s x := by
  exact
    not_exists_smoothPressure_momentumEquation_zero_of_localizedNilpotentStreamVelocityField_germ_origin
      hvel htime

theorem localized_nilpotent_stream_germ_nonzero_interface_obstruction_regression
    (t : NSTime) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution 0,
      ((fun x : NSSpace => S.velocity t x) =ᶠ[𝓝 (0 : NSSpace)]
        fun x : NSSpace => localizedNilpotentStreamVelocityField 0 x) ∧
        ((fun x : NSSpace => timeVelocityDerivative S.velocity t x) =ᶠ[𝓝 (0 : NSSpace)]
          fun _ : NSSpace => 0) := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_localizedNilpotentStreamVelocityField_germ_stationary_at t

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
