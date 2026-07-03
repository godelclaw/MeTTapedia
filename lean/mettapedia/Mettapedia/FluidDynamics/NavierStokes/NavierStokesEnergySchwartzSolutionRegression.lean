import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolution

/-!
# Regression checks for slice-Schwartz concrete Navier-Stokes energy identity
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

namespace Regression

theorem schwartz_solution_cancellations_regression
    {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν) :
    (∀ t, ∫ x, pressureEnergyPairing S.velocity S.pressure t x ∂volume = 0) ∧
      (∀ t, ∫ x, convectionEnergyPairing S.velocity t x ∂volume = 0) := by
  exact
    ⟨S.pressureEnergyCancellation,
      S.convectionEnergyCancellation⟩

theorem schwartz_solution_coordinate_energy_identity_regression
    {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν) :
    ∀ t,
      HasDerivAt (normalizedKineticEnergy S.velocity)
        (-(coordinateEnergyDissipationRate S.velocity ν t)) t := by
  exact S.coordinateEnergyDissipationIdentity

theorem schwartz_solution_meaningful_identity_regression
    {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν) :
    ∀ t,
      Integrable (kineticEnergyDensity S.velocity t) ∧
        HasDerivAt (normalizedKineticEnergy S.velocity)
          (-(coordinateEnergyDissipationRate S.velocity ν t)) t := by
  exact S.meaningfulCoordinateEnergyDissipationIdentity

theorem schwartz_solution_kinetic_energy_monotone_regression
    {ν : ℝ} (hν : 0 ≤ ν) (S : SchwartzConcreteNavierStokesSolution ν)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    kineticEnergyAt S.velocity t₁ ≤ kineticEnergyAt S.velocity t₀ := by
  exact S.kineticEnergyAt_le_of_le hν ht

theorem schwartz_solution_packet_regression
    {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν) :
    (∀ t, ∫ x, pressureEnergyPairing S.velocity S.pressure t x ∂volume = 0) ∧
      (∀ t, ∫ x, convectionEnergyPairing S.velocity t x ∂volume = 0) ∧
      CoordinateViscousEnergyPairingFormula S.velocity ∧
      ∀ t,
        HasDerivAt (normalizedKineticEnergy S.velocity)
          (-(coordinateEnergyDissipationRate S.velocity ν t)) t := by
  exact S.cancellation_and_coordinateEnergyDissipation_packet

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
