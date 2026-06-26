import Mettapedia.FluidDynamics.NavierStokes.Scaling.Basic

/-!
# Navier-Stokes Reynolds-stress obstruction

This module makes the current finite-energy/BKM route's missing Reynolds-stress
closure obligation first-class in the scaling cheap-falsification layer.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

theorem requiredWorldInterface_reynoldsStressClosure :
    NavierAveragedEquationObligation.reynoldsStressClosure.requiredWorldInterface =
      .reynoldsStressClosureWitness := by
  rfl

theorem currentNavierEnergyBKMAveragedEquationCompatibility_missing_reynoldsStressClosure :
    NavierAveragedEquationObligation.reynoldsStressClosure ∈
      currentNavierEnergyBKMAveragedEquationCompatibilityStatus.missingObligations := by
  simp [currentNavierEnergyBKMAveragedEquationCompatibility_missingObligations]

theorem currentNavierEnergyBKMAveragedEquationCompatibility_not_represented_reynoldsStressClosure :
    ¬ NavierAveragedEquationObligation.reynoldsStressClosure ∈
      currentNavierEnergyBKMAveragedEquationCompatibilityStatus.represented := by
  exact
    NavierAveragedEquationCompatibilityStatus.not_represented_of_mem_missingObligations
      currentNavierEnergyBKMAveragedEquationCompatibility_missing_reynoldsStressClosure

theorem currentNavierEnergyBKMRouteWorldInterfaces_missing_reynoldsStressClosureWitness :
    NavierScalingWorldInterface.reynoldsStressClosureWitness ∈
      currentNavierEnergyBKMRouteWorldInterfaces.missingFor .averagedEquationCompatibility := by
  simp [NavierScalingRouteWorldInterfaces.missingFor,
    currentNavierEnergyBKMRouteWorldInterfaces,
    NavierScalingCheck.requiredWorldInterfaces]

theorem currentNavierEnergyBKMRouteWorldInterfaces_not_supplied_reynoldsStressClosureWitness :
    ¬ NavierScalingWorldInterface.reynoldsStressClosureWitness ∈
      currentNavierEnergyBKMRouteWorldInterfaces.supplied := by
  exact
    NavierScalingRouteWorldInterfaces.not_supplied_of_mem_missingFor
      currentNavierEnergyBKMRouteWorldInterfaces_missing_reynoldsStressClosureWitness

/-- The current finite-energy/BKM route cannot use averaged-equation evidence
as a global-regularity promotion while Reynolds-stress closure is missing from
both the averaged-obligation ledger and the challenge-world interface layer. -/
theorem currentNavierEnergyBKMRoute_reynoldsStressClosure_obstruction :
    NavierAveragedEquationObligation.reynoldsStressClosure ∈
        currentNavierEnergyBKMAveragedEquationCompatibilityStatus.missingObligations ∧
      ¬ NavierAveragedEquationObligation.reynoldsStressClosure ∈
        currentNavierEnergyBKMAveragedEquationCompatibilityStatus.represented ∧
      NavierAveragedEquationObligation.reynoldsStressClosure.requiredWorldInterface =
        .reynoldsStressClosureWitness ∧
      NavierScalingWorldInterface.reynoldsStressClosureWitness ∈
        currentNavierEnergyBKMRouteWorldInterfaces.missingFor .averagedEquationCompatibility ∧
      ¬ NavierScalingWorldInterface.reynoldsStressClosureWitness ∈
        currentNavierEnergyBKMRouteWorldInterfaces.supplied := by
  exact
    ⟨currentNavierEnergyBKMAveragedEquationCompatibility_missing_reynoldsStressClosure,
      currentNavierEnergyBKMAveragedEquationCompatibility_not_represented_reynoldsStressClosure,
      requiredWorldInterface_reynoldsStressClosure,
      currentNavierEnergyBKMRouteWorldInterfaces_missing_reynoldsStressClosureWitness,
      currentNavierEnergyBKMRouteWorldInterfaces_not_supplied_reynoldsStressClosureWitness⟩

end NavierStokes
end FluidDynamics
end Mettapedia
