import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzAntiProfileCanaryObstruction

/-!
# Regression checks for anti-profile nonzero-canary obstruction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace Regression

open scoped ContDiff LineDeriv SchwartzMap

theorem localized_stream_antiprofile_velocity_zero_regression :
    twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1)
        nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile =
      (0 : NSVelocityField) := by
  exact localizedStreamAntiProfile_velocity_zero

theorem antiprofile_velocity_nonzero_iff_amplitudes_differ_regression
    (a b : NSTime → ℝ) :
    (∃ t x,
      twoModeSchwartzVelocity a b
          nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile t x ≠
        0) ↔
      ∃ t, a t ≠ b t := by
  exact localizedStreamAntiProfile_velocity_nonzero_iff_exists_amplitude_ne a b

theorem equal_amplitude_antiprofile_excluded_from_nonzero_solution_regression
    {ν : ℝ} (a : NSTime → ℝ) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      S.velocity =
        twoModeSchwartzVelocity a a
          nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile := by
  simpa [nsLocalizedStreamAntiProfile] using
    not_exists_nonzeroSchwartzConcreteSolution_equalAmplitudeAntiProfileVelocity
      (ν := ν) a nsLocalizedStreamDivergenceFreeInitialVelocity.1

theorem localized_stream_antiprofile_nonzero_solution_forces_amplitude_ne_regression
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (a b : NSTime → ℝ)
    (hS : S.velocity =
      twoModeSchwartzVelocity a b
        nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile) :
    ∃ t, a t ≠ b t := by
  exact
    nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_forces_amplitude_ne
      S a b hS

theorem localized_stream_antiprofile_endpoint_amplitude_difference_strict_drop_regression
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (a b : NSTime → ℝ)
    (hS : S.velocity =
      twoModeSchwartzVelocity a b
        nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile) :
    ∃ T xT,
      S.velocity T xT ≠ 0 ∧
        ∀ {s t : NSTime}, s < t → t ≤ T →
          (a t - b t) ^ (2 : ℕ) < (a s - b s) ^ (2 : ℕ) := by
  exact
    nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_exists_nonzero_endpoint_with_amplitudeDifference_sq_strict_drop
      hν S a b hS

theorem localized_stream_antiprofile_no_nondecreasing_amplitude_difference_before_endpoint_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ (a b : NSTime → ℝ),
        S.velocity =
          twoModeSchwartzVelocity a b
            nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile ∧
          ∃ s t T : NSTime,
            s < t ∧ t ≤ T ∧
              (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
                (a s - b s) ^ (2 : ℕ) ≤ (a t - b t) ^ (2 : ℕ) := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_amplitudeDifference_sq_nondecrease_before_nonzero_endpoint_of_pos_viscosity
      hν

theorem localized_stream_antiprofile_closure_packet_regression
    (ν : ℝ) :
    (∃ x : NSSpace, nsLocalizedStreamDivergenceFreeInitialVelocity.1 x ≠ 0) ∧
      (∃ x : NSSpace, nsLocalizedStreamAntiProfile x ≠ 0) ∧
      (∀ x, initialSpatialDivergence
        (nsLocalizedStreamDivergenceFreeInitialVelocity.1 : NSInitialVelocity) x = 0) ∧
      (∀ x, initialSpatialDivergence (nsLocalizedStreamAntiProfile : NSInitialVelocity) x = 0) ∧
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1)
          nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile =
        (0 : NSVelocityField) := by
  exact
    ⟨(localizedStreamAntiProfile_nonzeroProfiles_divergenceFree_closure_but_zeroVelocity ν).1,
      (localizedStreamAntiProfile_nonzeroProfiles_divergenceFree_closure_but_zeroVelocity ν).2.1,
      (localizedStreamAntiProfile_nonzeroProfiles_divergenceFree_closure_but_zeroVelocity ν).2.2.1,
      (localizedStreamAntiProfile_nonzeroProfiles_divergenceFree_closure_but_zeroVelocity ν).2.2.2.1,
      (localizedStreamAntiProfile_nonzeroProfiles_divergenceFree_closure_but_zeroVelocity ν).2.2.2.2.1⟩

theorem localized_stream_antiprofile_not_nonzero_solution_regression
    {ν : ℝ} :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      S.velocity =
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1)
          nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile := by
  exact not_exists_nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity

end Regression
end NavierStokes
end FluidDynamics
end Mettapedia
