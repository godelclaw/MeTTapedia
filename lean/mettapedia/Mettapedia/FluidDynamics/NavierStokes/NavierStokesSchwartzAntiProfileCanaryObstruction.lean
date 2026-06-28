import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolutionKernel
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzLocalizedStreamFunction

/-!
# Anti-Profile Nonzero-Canary Obstruction

This module closes a profile-level false positive in the nonzero
slice-Schwartz energy lane.  The localized stream-function seed gives a
nonzero divergence-free Schwartz profile `f`.  Pairing it with `-f` at equal
amplitudes gives nonzero profiles and a checked pressure-slice residual
closure, but the resulting two-mode velocity field is identically zero.

The nonzero solution interface therefore must track nonzero velocity, not just
nonzero component profiles or a residual expansion that cancels after
reconstruction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff LineDeriv SchwartzMap

namespace NonzeroSchwartzConcreteNavierStokesSolution

/-- The nonzero interface implies the reconstructed velocity field itself is
not identically zero. -/
theorem velocity_ne_zero {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν) :
    S.velocity ≠ (0 : NSVelocityField) := by
  intro hzero
  rcases S.nonzero_velocity with ⟨t, x, hne⟩
  exact hne (by simp [hzero])

end NonzeroSchwartzConcreteNavierStokesSolution

/-- The anti-profile of the localized divergence-free stream seed. -/
def nsLocalizedStreamAntiProfile : NSSchwartzInitialVelocity :=
  -nsLocalizedStreamDivergenceFreeInitialVelocity.1

theorem nsLocalizedStreamAntiProfile_nonzero :
    ∃ x : NSSpace, nsLocalizedStreamAntiProfile x ≠ 0 := by
  rcases nsLocalizedStreamDivergenceFreeInitialVelocity_nonzero with ⟨x, hx⟩
  exact ⟨x, by
    dsimp [nsLocalizedStreamAntiProfile]
    exact neg_ne_zero.mpr hx⟩

theorem initialSpatialDivergence_nsLocalizedStreamAntiProfile
    (x : NSSpace) :
    initialSpatialDivergence (nsLocalizedStreamAntiProfile : NSInitialVelocity) x = 0 := by
  have hfun :
      (nsLocalizedStreamAntiProfile : NSInitialVelocity) =
        - (nsLocalizedStreamDivergenceFreeInitialVelocity.1 : NSInitialVelocity) := by
    funext y
    simp [nsLocalizedStreamAntiProfile]
  rw [hfun]
  have h :=
    initialSpatialDivergence_const_smul (-1 : ℝ)
      (nsLocalizedStreamDivergenceFreeInitialVelocity.1 : NSInitialVelocity) x
  simpa [nsLocalizedStreamDivergenceFreeInitialVelocity.2 x] using h

/-- Equal-amplitude localized stream/anti-stream profiles reconstruct the zero
space-time velocity field. -/
theorem localizedStreamAntiProfile_velocity_zero :
    twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1)
        nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile =
      (0 : NSVelocityField) := by
  simpa [nsLocalizedStreamAntiProfile] using
    oneOneAntiProfileSchwartzVelocity_zero
      nsLocalizedStreamDivergenceFreeInitialVelocity.1

/-- The equal-amplitude localized stream/anti-stream pair satisfies the
expanded pressure-slice residual closure with zero pressure, despite
reconstructing the zero velocity field. -/
theorem localizedStreamAntiProfile_pressureSliceClosure_zeroPressure
    (ν : ℝ) :
    ∀ t x,
        spatialConvection
            (timeIndependentVelocity
              (nsLocalizedStreamDivergenceFreeInitialVelocity.1 : NSInitialVelocity)) t x +
            spatialFDeriv
              (timeIndependentVelocity
                (nsLocalizedStreamDivergenceFreeInitialVelocity.1 : NSInitialVelocity))
              t x (nsLocalizedStreamAntiProfile x) +
            spatialFDeriv
              (timeIndependentVelocity (nsLocalizedStreamAntiProfile : NSInitialVelocity))
              t x (nsLocalizedStreamDivergenceFreeInitialVelocity.1 x) +
            spatialConvection
              (timeIndependentVelocity (nsLocalizedStreamAntiProfile : NSInitialVelocity)) t x +
          spatialPressureGradient
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) t x =
        (ν : ℝ) •
          (spatialLaplacian
              (timeIndependentVelocity
                (nsLocalizedStreamDivergenceFreeInitialVelocity.1 : NSInitialVelocity)) t x +
            spatialLaplacian
              (timeIndependentVelocity (nsLocalizedStreamAntiProfile : NSInitialVelocity)) t x) := by
  simpa [nsLocalizedStreamAntiProfile] using
    explicitClosure_oneOneAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
      ν nsLocalizedStreamDivergenceFreeInitialVelocity.1

/-- A nonzero slice-Schwartz concrete solution cannot use the cancelled
localized stream/anti-stream velocity field. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity
    {ν : ℝ} :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      S.velocity =
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1)
          nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile := by
  rintro ⟨S, hS⟩
  exact S.velocity_ne_zero (by
    rw [hS, localizedStreamAntiProfile_velocity_zero])

/-- The anti-profile obstruction packet used by ProofState and regressions. -/
def LocalizedStreamAntiProfileCanaryObstructionPacket (ν : ℝ) : Prop :=
  (∃ x : NSSpace, nsLocalizedStreamDivergenceFreeInitialVelocity.1 x ≠ 0) ∧
    (∃ x : NSSpace, nsLocalizedStreamAntiProfile x ≠ 0) ∧
    (∀ x, initialSpatialDivergence
      (nsLocalizedStreamDivergenceFreeInitialVelocity.1 : NSInitialVelocity) x = 0) ∧
    (∀ x, initialSpatialDivergence (nsLocalizedStreamAntiProfile : NSInitialVelocity) x = 0) ∧
    twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1)
        nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile =
      (0 : NSVelocityField) ∧
    (∀ t x,
      spatialConvection
          (timeIndependentVelocity
            (nsLocalizedStreamDivergenceFreeInitialVelocity.1 : NSInitialVelocity)) t x +
          spatialFDeriv
            (timeIndependentVelocity
              (nsLocalizedStreamDivergenceFreeInitialVelocity.1 : NSInitialVelocity))
            t x (nsLocalizedStreamAntiProfile x) +
          spatialFDeriv
            (timeIndependentVelocity (nsLocalizedStreamAntiProfile : NSInitialVelocity))
            t x (nsLocalizedStreamDivergenceFreeInitialVelocity.1 x) +
          spatialConvection
            (timeIndependentVelocity (nsLocalizedStreamAntiProfile : NSInitialVelocity)) t x +
        spatialPressureGradient
          (fun s : NSTime => fun y : NSSpace =>
            (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) t x =
      (ν : ℝ) •
        (spatialLaplacian
            (timeIndependentVelocity
              (nsLocalizedStreamDivergenceFreeInitialVelocity.1 : NSInitialVelocity)) t x +
          spatialLaplacian
            (timeIndependentVelocity (nsLocalizedStreamAntiProfile : NSInitialVelocity)) t x))

/-- Combined anti-vacuity packet: the localized stream/anti-stream pair has
nonzero divergence-free Schwartz profiles and a pressure-slice residual
closure, but its reconstructed velocity is zero. -/
theorem localizedStreamAntiProfile_nonzeroProfiles_divergenceFree_closure_but_zeroVelocity
    (ν : ℝ) :
    LocalizedStreamAntiProfileCanaryObstructionPacket ν := by
  exact
    ⟨nsLocalizedStreamDivergenceFreeInitialVelocity_nonzero,
      nsLocalizedStreamAntiProfile_nonzero,
      nsLocalizedStreamDivergenceFreeInitialVelocity.2,
      initialSpatialDivergence_nsLocalizedStreamAntiProfile,
      localizedStreamAntiProfile_velocity_zero,
      localizedStreamAntiProfile_pressureSliceClosure_zeroPressure ν⟩

end NavierStokes
end FluidDynamics
end Mettapedia
