import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzNonzeroSupport
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

/-- Any reconstructed velocity field that is identically zero is excluded from
the nonzero slice-Schwartz concrete solution interface. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_of_velocity_eq_zero
    {ν : ℝ} {u : NSVelocityField} (hzero : u = 0) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν, S.velocity = u := by
  rintro ⟨S, hS⟩
  exact S.velocity_ne_zero (by rw [hS, hzero])

/-- Equal-amplitude anti-profile two-mode velocities can never be the velocity
field of a nonzero slice-Schwartz concrete solution. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_equalAmplitudeAntiProfileVelocity
    {ν : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      S.velocity = twoModeSchwartzVelocity a a f (-f) := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_of_velocity_eq_zero
      (equalAmplitudeAntiProfileSchwartzVelocity_zero a f)

/-- More generally, any pointwise equal anti-profile amplitudes reconstruct the
zero velocity field and are excluded from the nonzero interface. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_antiProfileVelocity_of_forall_amplitude_eq
    {ν : ℝ} (a b : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (hab : ∀ t, a t = b t) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      S.velocity = twoModeSchwartzVelocity a b f (-f) := by
  have hzero : twoModeSchwartzVelocity a b f (-f) = (0 : NSVelocityField) := by
    funext t x
    simp [twoModeSchwartzVelocity, hab t]
  exact not_exists_nonzeroSchwartzConcreteSolution_of_velocity_eq_zero hzero

/-- Exact nonzero boundary for the anti-profile two-mode family: for a nonzero
profile, the reconstructed velocity is nonzero exactly when the two scalar
amplitudes differ at some time. -/
theorem antiProfileSchwartzVelocity_nonzero_iff_exists_amplitude_ne
    (a b : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (hf : ∃ x : NSSpace, f x ≠ 0) :
    (∃ t x, twoModeSchwartzVelocity a b f (-f) t x ≠ 0) ↔
      ∃ t, a t ≠ b t := by
  constructor
  · intro hnonzero
    by_contra hnone
    have hab : ∀ t, a t = b t := by
      intro t
      by_contra ht
      exact hnone ⟨t, ht⟩
    have hzero :=
      (antiProfileSchwartzVelocity_eq_zero_iff_equalAmplitude a b f hf).mpr hab
    rcases hnonzero with ⟨t, x, htx⟩
    exact htx (by
      have hpoint := congrFun (congrFun hzero t) x
      simpa using hpoint)
  · intro hab
    exact exists_antiProfileSchwartzVelocity_ne_zero_of_exists_amplitude_ne a b f hf hab

/-- Anti-profile reconstruction is exactly a one-profile reconstruction with
scalar amplitude `a-b`. -/
theorem antiProfileSchwartzVelocity_eq_scalarProfile_amplitudeDifference
    (a b : NSTime → ℝ) (f : NSSchwartzInitialVelocity) :
    twoModeSchwartzVelocity a b f (-f) =
      fun t x => (a t - b t) • f x := by
  funext t x
  have hneg : (-f : NSSchwartzInitialVelocity) x = -f x := rfl
  simp only [twoModeSchwartzVelocity, hneg, smul_neg]
  rw [sub_smul]
  simp [sub_eq_add_neg]

/-- Any nonzero slice-Schwartz concrete solution represented by a nonzero
anti-profile family must lie on the unequal-amplitude side of the boundary. -/
theorem nonzeroSchwartzConcreteSolution_antiProfileVelocity_forces_amplitude_ne
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (a b : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (hf : ∃ x : NSSpace, f x ≠ 0)
    (hS : S.velocity = twoModeSchwartzVelocity a b f (-f)) :
    ∃ t, a t ≠ b t := by
  have hnonzero :
      ∃ t x, twoModeSchwartzVelocity a b f (-f) t x ≠ 0 := by
    rcases S.nonzero_velocity with ⟨t, x, htx⟩
    exact ⟨t, x, by
      simpa [hS] using htx⟩
  exact (antiProfileSchwartzVelocity_nonzero_iff_exists_amplitude_ne a b f hf).mp hnonzero

/-- At positive viscosity, the anti-profile branch cannot use a constant
amplitude difference: if `a(t) - b(t)` is constant, the reconstructed velocity
is time independent and the positive-viscosity stationary obstruction rules it
out of the nonzero slice-Schwartz interface. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_antiProfileVelocity_of_const_amplitudeDifference
    {ν : ℝ} (hν : 0 < ν) (a b : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (c : ℝ)
    (hdiff : ∀ t : NSTime, a t - b t = c) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      S.velocity = twoModeSchwartzVelocity a b f (-f) := by
  have hvelocity :
      twoModeSchwartzVelocity a b f (-f) =
        timeIndependentVelocity (fun x : NSSpace => c • f x) := by
    funext t x
    simp [twoModeSchwartzVelocity, timeIndependentVelocity]
    rw [← hdiff t, sub_smul]
    rfl
  intro hS
  exact
    not_exists_nonzeroSchwartzConcreteSolution_velocity_timeIndependent_of_pos_viscosity
      (ν := ν) (u₀ := fun x : NSSpace => c • f x) hν
      (by
        rcases hS with ⟨S, hSvelocity⟩
        exact ⟨S, by simpa [hvelocity] using hSvelocity⟩)

/-- Positive form of the previous obstruction: any positive-viscosity nonzero
solution represented by an anti-profile family must have genuinely
time-varying amplitude difference. -/
theorem nonzeroSchwartzConcreteSolution_antiProfileVelocity_forces_amplitudeDifference_nonconstant
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (a b : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (hS : S.velocity = twoModeSchwartzVelocity a b f (-f)) :
    ∃ t₀ t₁ : NSTime, a t₀ - b t₀ ≠ a t₁ - b t₁ := by
  by_contra hnone
  have hdiff : ∀ t : NSTime, a t - b t = a 0 - b 0 := by
    intro t
    by_contra ht
    exact hnone ⟨t, 0, ht⟩
  exact
    (not_exists_nonzeroSchwartzConcreteSolution_antiProfileVelocity_of_const_amplitudeDifference
      hν a b f (a 0 - b 0) hdiff) ⟨S, hS⟩

/-- Positive-viscosity anti-profile endpoint boundary: before any later nonzero
endpoint, the squared amplitude difference must strictly decrease forward in
time.  This is the localized anti-profile version of the scalar one-profile
support law. -/
theorem nonzeroSchwartzConcreteSolution_antiProfileVelocity_amplitudeDifference_sq_strict_lt_before_nonzero_endpoint
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (a b : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (hS : S.velocity = twoModeSchwartzVelocity a b f (-f))
    {s t T : NSTime} (hst : s < t) (htT : t ≤ T)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    (a t - b t) ^ (2 : ℕ) < (a s - b s) ^ (2 : ℕ) := by
  have hvelocity : S.velocity = fun r y => (a r - b r) • f y := by
    rw [hS, antiProfileSchwartzVelocity_eq_scalarProfile_amplitudeDifference]
  exact
    S.scalarProfile_amplitude_sq_strict_lt_before_nonzero_endpoint_of_pos_viscosity
      hν f hvelocity hst htT hneT

/-- Existential anti-profile support packet: any positive-viscosity nonzero
anti-profile solution has a nonzero endpoint whose whole past support ray has
strictly decreasing squared amplitude difference. -/
theorem nonzeroSchwartzConcreteSolution_antiProfileVelocity_exists_nonzero_endpoint_with_amplitudeDifference_sq_strict_drop
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (a b : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (hS : S.velocity = twoModeSchwartzVelocity a b f (-f)) :
    ∃ T xT,
      S.velocity T xT ≠ 0 ∧
        ∀ {s t : NSTime}, s < t → t ≤ T →
          (a t - b t) ^ (2 : ℕ) < (a s - b s) ^ (2 : ℕ) := by
  have hvelocity : S.velocity = fun r y => (a r - b r) • f y := by
    rw [hS, antiProfileSchwartzVelocity_eq_scalarProfile_amplitudeDifference]
  exact
    S.exists_nonzero_endpoint_with_scalarProfile_amplitude_sq_strict_drop
      hν f hvelocity

/-- Global anti-profile no-go: a positive-viscosity nonzero anti-profile
candidate cannot have a nondecreasing squared amplitude-difference subinterval
before a later nonzero endpoint. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_antiProfileVelocity_amplitudeDifference_sq_nondecrease_before_nonzero_endpoint_of_pos_viscosity
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ (a b : NSTime → ℝ) (f : NSSchwartzInitialVelocity),
        S.velocity = twoModeSchwartzVelocity a b f (-f) ∧
          ∃ s t T : NSTime,
            s < t ∧ t ≤ T ∧
              (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
                (a s - b s) ^ (2 : ℕ) ≤ (a t - b t) ^ (2 : ℕ) := by
  rintro ⟨S, a, b, f, hS, s, t, T, hst, htT, hneT, hnondec⟩
  have hdrop :
      (a t - b t) ^ (2 : ℕ) < (a s - b s) ^ (2 : ℕ) :=
    nonzeroSchwartzConcreteSolution_antiProfileVelocity_amplitudeDifference_sq_strict_lt_before_nonzero_endpoint
      hν S a b f hS hst htT hneT
  exact not_lt_of_ge hnondec hdrop

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

/-- The localized stream/anti-stream family has a nonzero reconstructed
velocity exactly on the unequal-amplitude side. -/
theorem localizedStreamAntiProfile_velocity_nonzero_iff_exists_amplitude_ne
    (a b : NSTime → ℝ) :
    (∃ t x,
      twoModeSchwartzVelocity a b
          nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile t x ≠
        0) ↔
      ∃ t, a t ≠ b t := by
  simpa [nsLocalizedStreamAntiProfile] using
    antiProfileSchwartzVelocity_nonzero_iff_exists_amplitude_ne
      a b nsLocalizedStreamDivergenceFreeInitialVelocity.1
      nsLocalizedStreamDivergenceFreeInitialVelocity_nonzero

/-- Any nonzero solution represented by localized stream/anti-stream profiles
must use unequal scalar amplitudes somewhere. -/
theorem nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_forces_amplitude_ne
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (a b : NSTime → ℝ)
    (hS : S.velocity =
      twoModeSchwartzVelocity a b
        nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile) :
    ∃ t, a t ≠ b t := by
  simpa [nsLocalizedStreamAntiProfile] using
    nonzeroSchwartzConcreteSolution_antiProfileVelocity_forces_amplitude_ne
      S a b nsLocalizedStreamDivergenceFreeInitialVelocity.1
      nsLocalizedStreamDivergenceFreeInitialVelocity_nonzero
      (by simpa [nsLocalizedStreamAntiProfile] using hS)

/-- Positive-viscosity localized stream/anti-stream candidates must vary the
amplitude difference in time; a constant difference would be a forbidden
time-independent positive-viscosity nonzero solution. -/
theorem nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_forces_amplitudeDifference_nonconstant
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (a b : NSTime → ℝ)
    (hS : S.velocity =
      twoModeSchwartzVelocity a b
        nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile) :
    ∃ t₀ t₁ : NSTime, a t₀ - b t₀ ≠ a t₁ - b t₁ := by
  simpa [nsLocalizedStreamAntiProfile] using
    nonzeroSchwartzConcreteSolution_antiProfileVelocity_forces_amplitudeDifference_nonconstant
      hν S a b nsLocalizedStreamDivergenceFreeInitialVelocity.1
      (by simpa [nsLocalizedStreamAntiProfile] using hS)

/-- Endpoint support law specialized to the explicit localized stream/
anti-stream seed: any positive-viscosity nonzero inhabitant represented by
this pair has strictly decreasing squared amplitude difference before a later
nonzero endpoint. -/
theorem nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_amplitudeDifference_sq_strict_lt_before_nonzero_endpoint
    {ν : ℝ} (hν : 0 < ν)
    (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    (a b : NSTime → ℝ)
    (hS : S.velocity =
      twoModeSchwartzVelocity a b
        nsLocalizedStreamDivergenceFreeInitialVelocity.1 nsLocalizedStreamAntiProfile)
    {s t T : NSTime} (hst : s < t) (htT : t ≤ T)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    (a t - b t) ^ (2 : ℕ) < (a s - b s) ^ (2 : ℕ) := by
  exact
    nonzeroSchwartzConcreteSolution_antiProfileVelocity_amplitudeDifference_sq_strict_lt_before_nonzero_endpoint
      hν S a b nsLocalizedStreamDivergenceFreeInitialVelocity.1
      (by simpa [nsLocalizedStreamAntiProfile] using hS) hst htT hneT

/-- Existential endpoint support packet specialized to the localized
stream/anti-stream seed. -/
theorem nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_exists_nonzero_endpoint_with_amplitudeDifference_sq_strict_drop
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
    nonzeroSchwartzConcreteSolution_antiProfileVelocity_exists_nonzero_endpoint_with_amplitudeDifference_sq_strict_drop
      hν S a b nsLocalizedStreamDivergenceFreeInitialVelocity.1
      (by simpa [nsLocalizedStreamAntiProfile] using hS)

/-- Global localized anti-profile no-go: before a later nonzero endpoint, a
positive-viscosity exact localized stream/anti-stream candidate cannot have a
nondecreasing squared amplitude-difference subinterval. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_localizedStreamAntiProfileVelocity_amplitudeDifference_sq_nondecrease_before_nonzero_endpoint_of_pos_viscosity
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
  intro h
  apply
    not_exists_nonzeroSchwartzConcreteSolution_antiProfileVelocity_amplitudeDifference_sq_nondecrease_before_nonzero_endpoint_of_pos_viscosity
      hν
  rcases h with ⟨S, a, b, hS, hbad⟩
  exact
    ⟨S, a, b, nsLocalizedStreamDivergenceFreeInitialVelocity.1,
      by simpa [nsLocalizedStreamAntiProfile] using hS, hbad⟩

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
