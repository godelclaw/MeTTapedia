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
