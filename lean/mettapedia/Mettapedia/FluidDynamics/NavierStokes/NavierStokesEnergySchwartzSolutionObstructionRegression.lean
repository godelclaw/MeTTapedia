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

theorem zero_coordinate_enstrophy_schwartz_slice_zero_regression
    {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν)
    {t : NSTime} (henst : coordinateEnstrophyAt S.velocity t = 0) :
    ∀ x, S.velocity t x = 0 := by
  exact S.velocity_eq_zero_of_coordinateEnstrophyAt_eq_zero henst

theorem nonzero_velocity_schwartz_slice_enstrophy_pos_regression
    {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν)
    {t : NSTime} {x : NSSpace} (hne : S.velocity t x ≠ 0) :
    0 < coordinateEnstrophyAt S.velocity t := by
  exact S.coordinateEnstrophyAt_pos_of_velocity_ne_zero hne

theorem nonzero_velocity_schwartz_slice_dissipation_pos_regression
    {ν : ℝ} (hν : 0 < ν) (S : SchwartzConcreteNavierStokesSolution ν)
    {t : NSTime} {x : NSSpace} (hne : S.velocity t x ≠ 0) :
    0 < coordinateEnergyDissipationRate S.velocity ν t := by
  exact S.coordinateEnergyDissipationRate_pos_of_velocity_ne_zero hν hne

theorem schwartz_solution_zero_of_forall_energy_derivative_zero_regression
    {ν : ℝ} (hν : 0 < ν) (S : SchwartzConcreteNavierStokesSolution ν)
    (hzero : ∀ t : NSTime, HasDerivAt (normalizedKineticEnergy S.velocity) 0 t) :
    ∀ t x, S.velocity t x = 0 := by
  exact
    S.velocity_eq_zero_of_forall_normalizedKineticEnergy_hasDerivAt_zero_of_pos_viscosity
      hν hzero

theorem schwartz_solution_zero_of_const_energy_regression
    {ν : ℝ} (hν : 0 < ν) (S : SchwartzConcreteNavierStokesSolution ν)
    (hconst :
      ∃ E : ℝ, normalizedKineticEnergy S.velocity = fun _ : NSTime => E) :
    ∀ t x, S.velocity t x = 0 := by
  exact
    S.velocity_eq_zero_of_exists_const_normalizedKineticEnergy_of_pos_viscosity
      hν hconst

theorem schwartz_solution_momentum_pressure_residual_vorticity_zero_regression
    {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν) :
    ∀ t x, spatialVorticity (momentumPressureResidual ν S.velocity) t x = 0 := by
  exact S.momentumPressureResidual_spatialVorticity_zero

theorem not_exists_schwartz_solution_velocity_of_residual_curl_regression
    {ν : ℝ} {u : NSVelocityField}
    (hcurl :
      ∃ t : NSTime, ∃ x : NSSpace,
        spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ∃ S : SchwartzConcreteNavierStokesSolution ν, S.velocity = u := by
  exact
    not_exists_schwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero
      hcurl

theorem not_exists_nonzero_schwartz_solution_velocity_of_residual_curl_regression
    {ν : ℝ} {u : NSVelocityField}
    (hcurl :
      ∃ t : NSTime, ∃ x : NSSpace,
        spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν, S.velocity = u := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero
      hcurl

theorem undamped_unit_heat_shear_not_schwartz_solution_velocity_regression :
    ¬ ∃ S : SchwartzConcreteNavierStokesSolution 1,
      S.velocity = heatShearVelocityField 0 1 1 := by
  exact
    not_exists_schwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero
      ⟨0, 0,
        spatialVorticity_momentumPressureResidual_undampedUnitHeatShearVelocityField_origin_ne_zero⟩

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

theorem stationary_schwartz_solution_zero_of_pos_viscosity_regression
    {ν : ℝ} (hν : 0 < ν) (S : SchwartzConcreteNavierStokesSolution ν)
    {u₀ : NSInitialVelocity}
    (hvelocity : S.velocity = timeIndependentVelocity u₀) :
    ∀ t x, S.velocity t x = 0 := by
  exact
    S.velocity_eq_zero_of_velocity_timeIndependent_of_pos_viscosity
      hν hvelocity

theorem stationary_nonzero_schwartz_solution_zero_of_pos_viscosity_regression
    {ν : ℝ} (hν : 0 < ν) (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {u₀ : NSInitialVelocity}
    (hvelocity : S.velocity = timeIndependentVelocity u₀) :
    ∀ t x, S.velocity t x = 0 := by
  exact
    S.velocity_eq_zero_of_velocity_timeIndependent_of_pos_viscosity
      hν hvelocity

theorem nonzero_schwartz_solution_exists_dissipation_pos_regression
    {ν : ℝ} (hν : 0 < ν) (S : NonzeroSchwartzConcreteNavierStokesSolution ν) :
    ∃ t : NSTime, 0 < coordinateEnergyDissipationRate S.velocity ν t := by
  exact S.exists_coordinateEnergyDissipationRate_pos_of_pos_viscosity hν

theorem nonzero_schwartz_solution_exists_strict_energy_identity_regression
    {ν : ℝ} (hν : 0 < ν) (S : NonzeroSchwartzConcreteNavierStokesSolution ν) :
    ∃ t : NSTime,
      0 < coordinateEnergyDissipationRate S.velocity ν t ∧
        HasDerivAt (normalizedKineticEnergy S.velocity)
          (-(coordinateEnergyDissipationRate S.velocity ν t)) t ∧
        -(coordinateEnergyDissipationRate S.velocity ν t) < 0 := by
  exact S.exists_strict_coordinateEnergyDissipationIdentity_of_pos_viscosity hν

theorem nonzero_schwartz_solution_not_forall_energy_derivative_zero_regression
    {ν : ℝ} (hν : 0 < ν) (S : NonzeroSchwartzConcreteNavierStokesSolution ν) :
    ¬ ∀ t : NSTime, HasDerivAt (normalizedKineticEnergy S.velocity) 0 t := by
  exact S.not_forall_normalizedKineticEnergy_hasDerivAt_zero_of_pos_viscosity hν

theorem nonzero_schwartz_solution_not_const_energy_regression
    {ν : ℝ} (hν : 0 < ν) (S : NonzeroSchwartzConcreteNavierStokesSolution ν) :
    ¬ ∃ E : ℝ, normalizedKineticEnergy S.velocity = fun _ : NSTime => E := by
  exact S.not_exists_const_normalizedKineticEnergy_of_pos_viscosity hν

theorem not_exists_nonzero_schwartz_solution_forall_energy_derivative_zero_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∀ t : NSTime, HasDerivAt (normalizedKineticEnergy S.velocity) 0 t := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_forall_normalizedKineticEnergy_hasDerivAt_zero
      hν

theorem not_exists_nonzero_schwartz_solution_const_energy_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ E : ℝ, normalizedKineticEnergy S.velocity = fun _ : NSTime => E := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_const_normalizedKineticEnergy_of_pos_viscosity
      hν

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

theorem not_exists_nonzero_stationary_schwartz_solution_of_pos_viscosity_regression
    {ν : ℝ} (hν : 0 < ν) {u₀ : NSInitialVelocity} :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      S.velocity = timeIndependentVelocity u₀ := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_velocity_timeIndependent_of_pos_viscosity
      hν

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
