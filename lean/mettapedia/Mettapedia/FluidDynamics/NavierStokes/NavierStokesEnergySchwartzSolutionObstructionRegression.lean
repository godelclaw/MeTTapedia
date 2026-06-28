import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolutionObstruction

/-!
# Regression checks for the line-invariant slice-Schwartz obstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

namespace Regression

theorem lineInvariant_velocitySlice_zero_regression
    {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν)
    {t : NSTime} {v : NSSpace} (hv : v ≠ 0)
    (hinv : TranslationInvariantAlong v (fun x : NSSpace => S.velocitySlice t x)) :
    ∀ x, S.velocity t x = 0 := by
  exact S.velocity_eq_zero_of_velocitySlice_translationInvariantAlong hv hinv

theorem nonzero_schwartz_solution_not_all_lineInvariant_regression
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {v : NSSpace} (hv : v ≠ 0) :
    ¬ ∀ t : NSTime,
      TranslationInvariantAlong v (fun x : NSSpace => S.velocitySlice t x) := by
  exact S.not_all_velocitySlices_translationInvariantAlong hv

theorem nonzero_schwartz_solution_has_non_lineInvariant_slice_regression
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {v : NSSpace} (hv : v ≠ 0) :
    ∃ t : NSTime,
      ¬ TranslationInvariantAlong v (fun x : NSSpace => S.velocitySlice t x) := by
  exact every_nonzeroSchwartzConcreteSolution_has_non_lineInvariant_slice S hv

theorem stationary_schwartz_solution_dissipation_zero_regression
    {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν)
    {u₀ : NSInitialVelocity}
    (hvelocity : S.velocity = timeIndependentVelocity u₀) (t : NSTime) :
    coordinateEnergyDissipationRate S.velocity ν t = 0 := by
  exact
    S.coordinateEnergyDissipationRate_eq_zero_of_velocity_timeIndependent
      hvelocity t

theorem stationary_nonzero_schwartz_solution_dissipation_zero_regression
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {u₀ : NSInitialVelocity}
    (hvelocity : S.velocity = timeIndependentVelocity u₀) (t : NSTime) :
    coordinateEnergyDissipationRate S.velocity ν t = 0 := by
  exact
    S.coordinateEnergyDissipationRate_eq_zero_of_velocity_timeIndependent
      hvelocity t

theorem not_exists_nonzero_stationary_schwartz_solution_of_dissipation_ne_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hdiss :
      ∃ t : NSTime,
        coordinateEnergyDissipationRate (timeIndependentVelocity u₀) ν t ≠ 0) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      S.velocity = timeIndependentVelocity u₀ := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_velocity_timeIndependent_of_coordinateEnergyDissipationRate_ne_zero
      hdiss

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
