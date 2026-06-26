import Mettapedia.FluidDynamics.NavierStokes.Scaling.Basic

/-!
# Navier-Stokes energy-inequality obstruction

This module makes the current finite-energy/BKM route's missing
energy-inequality compatibility obligation first-class in the scaling
cheap-falsification layer.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

theorem requiredWorldInterface_energyInequalityCompatibility :
    NavierAveragedEquationObligation.energyInequalityCompatibility.requiredWorldInterface =
      .energyInequalityTransport := by
  rfl

theorem currentNavierEnergyBKMAveragedEquationCompatibility_missing_energyInequalityCompatibility :
    NavierAveragedEquationObligation.energyInequalityCompatibility ∈
      currentNavierEnergyBKMAveragedEquationCompatibilityStatus.missingObligations := by
  simp [currentNavierEnergyBKMAveragedEquationCompatibility_missingObligations]

theorem currentNavierEnergyBKMAveragedEquationCompatibility_not_represented_energyInequalityCompatibility :
    ¬ NavierAveragedEquationObligation.energyInequalityCompatibility ∈
      currentNavierEnergyBKMAveragedEquationCompatibilityStatus.represented := by
  exact
    NavierAveragedEquationCompatibilityStatus.not_represented_of_mem_missingObligations
      currentNavierEnergyBKMAveragedEquationCompatibility_missing_energyInequalityCompatibility

theorem currentNavierEnergyBKMRouteWorldInterfaces_missing_energyInequalityTransport :
    NavierScalingWorldInterface.energyInequalityTransport ∈
      currentNavierEnergyBKMRouteWorldInterfaces.missingFor .averagedEquationCompatibility := by
  simp [NavierScalingRouteWorldInterfaces.missingFor,
    currentNavierEnergyBKMRouteWorldInterfaces,
    NavierScalingCheck.requiredWorldInterfaces]

theorem currentNavierEnergyBKMRouteWorldInterfaces_not_supplied_energyInequalityTransport :
    ¬ NavierScalingWorldInterface.energyInequalityTransport ∈
      currentNavierEnergyBKMRouteWorldInterfaces.supplied := by
  exact
    NavierScalingRouteWorldInterfaces.not_supplied_of_mem_missingFor
      currentNavierEnergyBKMRouteWorldInterfaces_missing_energyInequalityTransport

/-- The current finite-energy/BKM route cannot use averaged-equation evidence
as a global-regularity promotion while energy-inequality compatibility is
missing from both the averaged-obligation ledger and the challenge-world
interface layer. -/
theorem currentNavierEnergyBKMRoute_energyInequalityCompatibility_obstruction :
    NavierAveragedEquationObligation.energyInequalityCompatibility ∈
        currentNavierEnergyBKMAveragedEquationCompatibilityStatus.missingObligations ∧
      ¬ NavierAveragedEquationObligation.energyInequalityCompatibility ∈
        currentNavierEnergyBKMAveragedEquationCompatibilityStatus.represented ∧
      NavierAveragedEquationObligation.energyInequalityCompatibility.requiredWorldInterface =
        .energyInequalityTransport ∧
      NavierScalingWorldInterface.energyInequalityTransport ∈
        currentNavierEnergyBKMRouteWorldInterfaces.missingFor .averagedEquationCompatibility ∧
      ¬ NavierScalingWorldInterface.energyInequalityTransport ∈
        currentNavierEnergyBKMRouteWorldInterfaces.supplied := by
  exact
    ⟨currentNavierEnergyBKMAveragedEquationCompatibility_missing_energyInequalityCompatibility,
      currentNavierEnergyBKMAveragedEquationCompatibility_not_represented_energyInequalityCompatibility,
      requiredWorldInterface_energyInequalityCompatibility,
      currentNavierEnergyBKMRouteWorldInterfaces_missing_energyInequalityTransport,
      currentNavierEnergyBKMRouteWorldInterfaces_not_supplied_energyInequalityTransport⟩

end NavierStokes
end FluidDynamics
end Mettapedia
