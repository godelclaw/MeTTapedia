import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolutionObstruction

/-!
# Regression checks for the line-invariant slice-Schwartz obstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap Topology

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

theorem nondegenerate_heat_shear_exists_nonzero_regression
    {ν a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ∃ t : NSTime, ∃ x : NSSpace, heatShearVelocityField ν a k t x ≠ 0 := by
  exact
    heatShearVelocityField_exists_nonzero_of_amplitude_ne_zero_of_wavenumber_ne_zero
      ha hk

theorem heat_shear_exact_but_not_schwartz_solution_velocity_regression
    {ν a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    (∃ t : NSTime, ∃ x : NSSpace, heatShearVelocityField ν a k t x ≠ 0) ∧
      (∀ t x, spatialDivergence (heatShearVelocityField ν a k) t x = 0) ∧
      (∀ t x,
        timeVelocityDerivative (heatShearVelocityField ν a k) t x +
            spatialConvection (heatShearVelocityField ν a k) t x +
            spatialPressureGradient (0 : NSPressureField) t x =
          ν • spatialLaplacian (heatShearVelocityField ν a k) t x) ∧
      (¬ ∃ S : SchwartzConcreteNavierStokesSolution ν,
        S.velocity = heatShearVelocityField ν a k) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        S.velocity = heatShearVelocityField ν a k) := by
  exact
    heatShearVelocityField_exact_nonzero_and_not_schwartzConcreteSolution
      ν ha hk

theorem heat_shear_wrong_viscosity_not_schwartz_solution_velocity_regression
    {μ ν a k : ℝ} (hμν : μ ≠ ν) (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ∃ S : SchwartzConcreteNavierStokesSolution μ,
      S.velocity = heatShearVelocityField ν a k := by
  exact
    not_exists_schwartzConcreteSolution_velocity_heatShearVelocityField_wrongViscosity
      hμν ha hk

theorem heat_shear_wrong_viscosity_not_nonzero_schwartz_solution_velocity_regression
    {μ ν a k : ℝ} (hμν : μ ≠ ν) (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution μ,
      S.velocity = heatShearVelocityField ν a k := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_velocity_heatShearVelocityField_wrongViscosity
      hμν ha hk

theorem oneOne_twoMode_schwartz_solution_lapSum_residual_curl_zero_regression
    {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν)
    (f g : NSSchwartzInitialVelocity)
    (hvelocity :
      S.velocity =
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    ∀ t x,
      spatialVorticity
        (fun s y =>
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) s y +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) s y)) t x =
        0 := by
  exact
    oneOneTwoModeSchwartzVelocity_lapSum_residualVorticity_zero_of_schwartzConcreteSolution
      S f g hvelocity hclosure

theorem oneOne_twoMode_residual_curl_not_schwartz_solution_regression
    {ν : ℝ} (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hcurl : ∃ t x,
      spatialVorticity
        (fun s y =>
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) s y +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) s y)) t x ≠
        0) :
    ¬ ∃ S : SchwartzConcreteNavierStokesSolution ν,
      S.velocity =
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g := by
  exact
    not_exists_schwartzConcreteSolution_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero
      f g hclosure hcurl

theorem oneOne_twoMode_residual_curl_not_nonzero_schwartz_solution_regression
    {ν : ℝ} (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hcurl : ∃ t x,
      spatialVorticity
        (fun s y =>
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) s y +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) s y)) t x ≠
        0) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      S.velocity =
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero
      f g hclosure hcurl

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

theorem schwartz_solution_dissipation_pos_of_nonzero_slice_regression
    {ν : ℝ} (hν : 0 < ν) (S : SchwartzConcreteNavierStokesSolution ν)
    {t : NSTime}
    (hne : ∃ x : NSSpace, S.velocity t x ≠ 0) :
    0 < coordinateEnergyDissipationRate S.velocity ν t := by
  exact S.coordinateEnergyDissipationRate_pos_of_exists_velocity_ne_zero hν hne

theorem schwartz_solution_energy_derivative_lt_zero_of_nonzero_slice_regression
    {ν : ℝ} (hν : 0 < ν) (S : SchwartzConcreteNavierStokesSolution ν)
    {t d : ℝ}
    (hne : ∃ x : NSSpace, S.velocity t x ≠ 0)
    (hderiv : HasDerivAt (normalizedKineticEnergy S.velocity) d t) :
    d < 0 := by
  exact
    S.normalizedKineticEnergy_derivative_lt_zero_of_exists_velocity_ne_zero
      hν hne hderiv

theorem nonzero_schwartz_solution_energy_derivative_lt_zero_of_nonzero_slice_regression
    {ν : ℝ} (hν : 0 < ν) (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {t d : ℝ}
    (hne : ∃ x : NSSpace, S.velocity t x ≠ 0)
    (hderiv : HasDerivAt (normalizedKineticEnergy S.velocity) d t) :
    d < 0 := by
  exact
    S.normalizedKineticEnergy_derivative_lt_zero_of_exists_velocity_ne_zero
      hν hne hderiv

theorem schwartz_solution_energy_eventually_right_lt_of_nonzero_slice_regression
    {ν : ℝ} (hν : 0 < ν) (S : SchwartzConcreteNavierStokesSolution ν)
    {t : NSTime}
    (hne : ∃ x : NSSpace, S.velocity t x ≠ 0) :
    ∀ᶠ s in 𝓝[>] t,
      normalizedKineticEnergy S.velocity s <
        normalizedKineticEnergy S.velocity t := by
  exact
    S.normalizedKineticEnergy_eventually_right_lt_of_exists_velocity_ne_zero
      hν hne

theorem schwartz_solution_energy_right_drop_sample_of_nonzero_slice_regression
    {ν : ℝ} (hν : 0 < ν) (S : SchwartzConcreteNavierStokesSolution ν)
    {t ε : NSTime}
    (hne : ∃ x : NSSpace, S.velocity t x ≠ 0) (hε : 0 < ε) :
    ∃ s, t < s ∧ s < t + ε ∧
      normalizedKineticEnergy S.velocity s <
        normalizedKineticEnergy S.velocity t := by
  exact
    S.exists_normalizedKineticEnergy_right_drop_sample_of_exists_velocity_ne_zero
      hν hne hε

theorem nonzero_schwartz_solution_energy_right_drop_sample_at_nonzero_regression
    {ν : ℝ} (hν : 0 < ν) (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {t ε : NSTime} {x : NSSpace}
    (hne : S.velocity t x ≠ 0) (hε : 0 < ε) :
    ∃ s, t < s ∧ s < t + ε ∧
      normalizedKineticEnergy S.velocity s <
        normalizedKineticEnergy S.velocity t := by
  exact
    S.exists_normalizedKineticEnergy_right_drop_sample_at_nonzero_of_pos_viscosity
      hν hne hε

theorem schwartz_solution_energy_strict_future_drop_of_nonzero_slice_regression
    {ν : ℝ} (hν : 0 < ν) (S : SchwartzConcreteNavierStokesSolution ν)
    {t₀ t₁ : NSTime}
    (hne : ∃ x : NSSpace, S.velocity t₀ x ≠ 0) (ht : t₀ < t₁) :
    normalizedKineticEnergy S.velocity t₁ <
      normalizedKineticEnergy S.velocity t₀ := by
  exact
    S.normalizedKineticEnergy_strict_lt_of_exists_velocity_ne_zero_left
      hν hne ht

theorem nonzero_schwartz_solution_energy_strict_future_drop_at_nonzero_regression
    {ν : ℝ} (hν : 0 < ν) (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {t₀ t₁ : NSTime} {x : NSSpace}
    (hne : S.velocity t₀ x ≠ 0) (ht : t₀ < t₁) :
    normalizedKineticEnergy S.velocity t₁ <
      normalizedKineticEnergy S.velocity t₀ := by
  exact
    S.normalizedKineticEnergy_strict_lt_after_nonzero_of_pos_viscosity
      hν hne ht

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

theorem schwartz_solution_local_min_energy_slice_zero_regression
    {ν : ℝ} (hν : 0 < ν) (S : SchwartzConcreteNavierStokesSolution ν)
    {t : NSTime}
    (hmin : IsLocalMin (normalizedKineticEnergy S.velocity) t) :
    ∀ x, S.velocity t x = 0 := by
  exact
    S.velocity_eq_zero_of_isLocalMin_normalizedKineticEnergy_of_pos_viscosity
      hν hmin

theorem schwartz_solution_local_max_energy_slice_zero_regression
    {ν : ℝ} (hν : 0 < ν) (S : SchwartzConcreteNavierStokesSolution ν)
    {t : NSTime}
    (hmax : IsLocalMax (normalizedKineticEnergy S.velocity) t) :
    ∀ x, S.velocity t x = 0 := by
  exact
    S.velocity_eq_zero_of_isLocalMax_normalizedKineticEnergy_of_pos_viscosity
      hν hmax

theorem schwartz_solution_energy_plateau_slice_zero_regression
    {ν : ℝ} (hν : 0 < ν) (S : SchwartzConcreteNavierStokesSolution ν)
    {t : NSTime}
    (hplateau : ∀ᶠ s in nhds t,
      normalizedKineticEnergy S.velocity s =
        normalizedKineticEnergy S.velocity t) :
    ∀ x, S.velocity t x = 0 := by
  exact
    S.velocity_eq_zero_of_eventually_eq_normalizedKineticEnergy_of_pos_viscosity
      hν hplateau

theorem nonzero_schwartz_solution_not_local_min_at_nonzero_regression
    {ν : ℝ} (hν : 0 < ν) (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {t : NSTime} {x : NSSpace}
    (hne : S.velocity t x ≠ 0) :
    ¬ IsLocalMin (normalizedKineticEnergy S.velocity) t := by
  exact S.not_isLocalMin_normalizedKineticEnergy_at_nonzero_of_pos_viscosity
    hν hne

theorem nonzero_schwartz_solution_not_local_max_at_nonzero_regression
    {ν : ℝ} (hν : 0 < ν) (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {t : NSTime} {x : NSSpace}
    (hne : S.velocity t x ≠ 0) :
    ¬ IsLocalMax (normalizedKineticEnergy S.velocity) t := by
  exact S.not_isLocalMax_normalizedKineticEnergy_at_nonzero_of_pos_viscosity
    hν hne

theorem nonzero_schwartz_solution_not_energy_plateau_at_nonzero_regression
    {ν : ℝ} (hν : 0 < ν) (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {t : NSTime} {x : NSSpace}
    (hne : S.velocity t x ≠ 0) :
    ¬ ∀ᶠ s in nhds t,
      normalizedKineticEnergy S.velocity s =
        normalizedKineticEnergy S.velocity t := by
  exact
    S.not_eventually_eq_normalizedKineticEnergy_at_nonzero_of_pos_viscosity
      hν hne

theorem nonzero_schwartz_solution_not_eventually_right_energy_nondecreasing_at_nonzero_regression
    {ν : ℝ} (hν : 0 < ν) (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {t : NSTime} {x : NSSpace}
    (hne : S.velocity t x ≠ 0) :
    ¬ ∀ᶠ s in 𝓝[>] t,
      normalizedKineticEnergy S.velocity t ≤
        normalizedKineticEnergy S.velocity s := by
  exact
    S.not_eventually_right_normalizedKineticEnergy_nondecreasing_at_nonzero_of_pos_viscosity
      hν hne

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

theorem not_exists_nonzero_schwartz_solution_nonzero_local_min_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ t x,
        S.velocity t x ≠ 0 ∧
          IsLocalMin (normalizedKineticEnergy S.velocity) t := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_nonzero_localMin_energy_of_pos_viscosity
      hν

theorem not_exists_nonzero_schwartz_solution_nonzero_local_max_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ t x,
        S.velocity t x ≠ 0 ∧
          IsLocalMax (normalizedKineticEnergy S.velocity) t := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_nonzero_localMax_energy_of_pos_viscosity
      hν

theorem not_exists_nonzero_schwartz_solution_nonzero_nonneg_energy_derivative_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ t x d,
        S.velocity t x ≠ 0 ∧
          HasDerivAt (normalizedKineticEnergy S.velocity) d t ∧
            0 ≤ d := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_nonzero_nonneg_energy_derivative_of_pos_viscosity
      hν

theorem not_exists_nonzero_schwartz_solution_nonzero_energy_plateau_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ t x,
        S.velocity t x ≠ 0 ∧
          (∀ᶠ s in nhds t,
            normalizedKineticEnergy S.velocity s =
              normalizedKineticEnergy S.velocity t) := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_nonzero_energy_plateau_of_pos_viscosity
      hν

theorem not_exists_nonzero_schwartz_solution_nonzero_eventually_right_energy_nondecreasing_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ t x,
        S.velocity t x ≠ 0 ∧
          (∀ᶠ s in 𝓝[>] t,
            normalizedKineticEnergy S.velocity t ≤
              normalizedKineticEnergy S.velocity s) := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_nonzero_eventually_right_energy_nondecreasing_of_pos_viscosity
      hν

theorem not_exists_nonzero_schwartz_solution_nonzero_later_energy_nondecreasing_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ t₀ t₁ x,
        S.velocity t₀ x ≠ 0 ∧
          t₀ < t₁ ∧
            normalizedKineticEnergy S.velocity t₀ ≤
              normalizedKineticEnergy S.velocity t₁ := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_nonzero_later_energy_nondecreasing_of_pos_viscosity
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
