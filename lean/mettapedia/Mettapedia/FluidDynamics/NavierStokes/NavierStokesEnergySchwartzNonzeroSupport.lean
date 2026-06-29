import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzPastDissipation

/-!
# Slice-Schwartz Nonzero Time-Support Kernel

This module promotes the zero-restart and past-dissipation consequences into an
endpoint-parametric support API.  A later nonzero slice forces every earlier
slice to be nonzero somewhere; at positive viscosity, every nontrivial forward
interval ending before that later nonzero endpoint has strict normalized-energy
drop.

The result is a structural constraint for future nonzero canary searches.  It
does not construct a positive-viscosity nonzero slice-Schwartz solution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap Topology

/-- A nonzero Schwartz velocity profile has strictly positive `L^2` mass. -/
theorem integral_norm_sq_pos_of_schwartz_ne_zero
    (f : NSSchwartzInitialVelocity) (hf : ∃ x : NSSpace, f x ≠ 0) :
    0 < ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume := by
  rcases hf with ⟨x, hx⟩
  exact
    MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
      (x := x)
      (f.continuous.norm.pow 2)
      (integrable_norm_sq_of_schwartz f)
      (fun y => by positivity)
      (by simp [hx])

/-- Normalized kinetic energy for a scalar-modulated Schwartz profile. -/
theorem normalizedKineticEnergy_scalar_smul_schwartz
    (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity) :
    normalizedKineticEnergy (fun t x => a t • f x) =
      fun t =>
        (1 / 2 : ℝ) *
          ((a t) ^ (2 : ℕ) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume) := by
  funext t
  rw [normalizedKineticEnergy, kineticEnergyAt_scalar_smul_schwartz a f]

/-- Reusable support-order kernel for the concrete slice-Schwartz interface:
zero slices are future-absorbing at nonnegative viscosity, and positive
viscosity turns any later nonzero endpoint into strict energy drop on every
earlier nontrivial interval. -/
structure SchwartzNonzeroTimeSupportKernel
    (ν : ℝ) (u : NSVelocityField) (p : NSPressureField) where
  concrete : SchwartzConcreteSolutionKernel ν u p
  zeroRestart : SchwartzZeroRestartKernel ν u p
  nonzeroBeforeEndpoint :
    0 ≤ ν → ∀ {t₀ t₁ : NSTime}, t₀ ≤ t₁ →
      (∃ x₁ : NSSpace, u t₁ x₁ ≠ 0) →
        ∃ x₀ : NSSpace, u t₀ x₀ ≠ 0
  strictEnergyDropBeforeEndpoint :
    0 < ν → ∀ {s t T : NSTime}, s < t → t ≤ T →
      (∃ xT : NSSpace, u T xT ≠ 0) →
        normalizedKineticEnergy u t < normalizedKineticEnergy u s

namespace SchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν)

/-- Endpoint-parametric positive form of zero-restart: if a later endpoint is
nonzero, then every earlier slice is nonzero somewhere. -/
theorem exists_velocity_ne_zero_at_or_before_nonzero_endpoint_of_nonneg_viscosity
    (hν : 0 ≤ ν) {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁)
    (hne₁ : ∃ x₁ : NSSpace, S.velocity t₁ x₁ ≠ 0) :
    ∃ x₀ : NSSpace, S.velocity t₀ x₀ ≠ 0 := by
  by_contra hnone
  have hzero : ∀ x : NSSpace, S.velocity t₀ x = 0 := by
    intro x
    by_contra hx
    exact hnone ⟨x, hx⟩
  rcases hne₁ with ⟨x₁, hx₁⟩
  have hzero₁ :
      S.velocity t₁ x₁ = 0 :=
    S.velocity_eq_zero_at_later_of_velocity_eq_zero_at_of_nonneg_viscosity
      hν ht hzero x₁
  exact hx₁ hzero₁

/-- Endpoint-parametric strict past-order form: before any later nonzero
endpoint of a positive-viscosity solution, normalized kinetic energy strictly
drops across every nontrivial forward subinterval. -/
theorem normalizedKineticEnergy_strict_lt_before_nonzero_endpoint_of_pos_viscosity
    (hν : 0 < ν) {s t T : NSTime} (hst : s < t) (htT : t ≤ T)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    normalizedKineticEnergy S.velocity t <
      normalizedKineticEnergy S.velocity s := by
  have hsT : s ≤ T := le_trans (le_of_lt hst) htT
  have hnes :
      ∃ xs : NSSpace, S.velocity s xs ≠ 0 :=
    S.exists_velocity_ne_zero_at_or_before_nonzero_endpoint_of_nonneg_viscosity
      hν.le hsT hneT
  exact
    S.normalizedKineticEnergy_strict_lt_of_exists_velocity_ne_zero_left
      hν hnes hst

/-- One-profile positive-viscosity boundary: if a concrete solution is a
scalar-modulated fixed Schwartz profile, then before any later nonzero
endpoint the squared scalar amplitude must strictly decrease forward in time.
This rules out separable positive-viscosity canary attempts with repeated
absolute amplitude on the whole-past support ray. -/
theorem scalarProfile_amplitude_sq_strict_lt_before_nonzero_endpoint_of_pos_viscosity
    (hν : 0 < ν) {a : NSTime → ℝ} (f : NSSchwartzInitialVelocity)
    (hvelocity : S.velocity = fun r y => a r • f y)
    {s t T : NSTime} (hst : s < t) (htT : t ≤ T)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    (a t) ^ (2 : ℕ) < (a s) ^ (2 : ℕ) := by
  have hdrop :
      normalizedKineticEnergy S.velocity t <
        normalizedKineticEnergy S.velocity s :=
    S.normalizedKineticEnergy_strict_lt_before_nonzero_endpoint_of_pos_viscosity
      hν hst htT hneT
  have hfne : ∃ x : NSSpace, f x ≠ 0 := by
    rcases hneT with ⟨xT, hxT⟩
    refine ⟨xT, ?_⟩
    intro hfx
    have hzero : S.velocity T xT = 0 := by
      rw [hvelocity]
      simp [hfx]
    exact hxT hzero
  let E : ℝ := ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume
  have hEpos : 0 < E := by
    dsimp [E]
    exact integral_norm_sq_pos_of_schwartz_ne_zero f hfne
  have htEnergy :
      normalizedKineticEnergy S.velocity t =
        (1 / 2 : ℝ) * ((a t) ^ (2 : ℕ) * E) := by
    rw [hvelocity]
    simpa [E] using
      congrFun (normalizedKineticEnergy_scalar_smul_schwartz a f) t
  have hsEnergy :
      normalizedKineticEnergy S.velocity s =
        (1 / 2 : ℝ) * ((a s) ^ (2 : ℕ) * E) := by
    rw [hvelocity]
    simpa [E] using
      congrFun (normalizedKineticEnergy_scalar_smul_schwartz a f) s
  rw [htEnergy, hsEnergy] at hdrop
  nlinarith

/-- The reusable nonzero time-support kernel carried by any concrete
slice-Schwartz solution. -/
def nonzeroTimeSupportKernel :
    SchwartzNonzeroTimeSupportKernel ν S.velocity S.pressure where
  concrete := S.concreteSolutionKernel
  zeroRestart := S.zeroRestartKernel
  nonzeroBeforeEndpoint := fun hν {_t₀ _t₁} ht hne =>
    S.exists_velocity_ne_zero_at_or_before_nonzero_endpoint_of_nonneg_viscosity
      hν ht hne
  strictEnergyDropBeforeEndpoint := fun hν {_s _t _T} hst htT hne =>
    S.normalizedKineticEnergy_strict_lt_before_nonzero_endpoint_of_pos_viscosity
      hν hst htT hne

end SchwartzConcreteNavierStokesSolution

namespace NonzeroSchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)

/-- Nonzero solutions inherit the endpoint-parametric support kernel. -/
def nonzeroTimeSupportKernel :
    SchwartzNonzeroTimeSupportKernel ν S.velocity S.pressure :=
  S.toSchwartzConcreteNavierStokesSolution.nonzeroTimeSupportKernel

/-- Nonzero-interface endpoint support: any later nonzero endpoint forces the
chosen earlier slice to be nonzero somewhere. -/
theorem exists_velocity_ne_zero_before_endpoint_of_nonneg_viscosity
    (hν : 0 ≤ ν) {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁)
    (hne₁ : ∃ x₁ : NSSpace, S.velocity t₁ x₁ ≠ 0) :
    ∃ x₀ : NSSpace, S.velocity t₀ x₀ ≠ 0 :=
  SchwartzConcreteNavierStokesSolution.exists_velocity_ne_zero_at_or_before_nonzero_endpoint_of_nonneg_viscosity
    S.toSchwartzConcreteNavierStokesSolution hν ht hne₁

/-- Nonzero-interface strict endpoint form: before any later nonzero endpoint,
positive viscosity forces strict normalized-energy drop on every earlier
nontrivial forward subinterval. -/
theorem normalizedKineticEnergy_strict_lt_before_nonzero_endpoint_of_pos_viscosity
    (hν : 0 < ν) {s t T : NSTime} (hst : s < t) (htT : t ≤ T)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    normalizedKineticEnergy S.velocity t <
      normalizedKineticEnergy S.velocity s :=
  SchwartzConcreteNavierStokesSolution.normalizedKineticEnergy_strict_lt_before_nonzero_endpoint_of_pos_viscosity
    S.toSchwartzConcreteNavierStokesSolution hν hst htT hneT

/-- Nonzero-interface one-profile amplitude boundary. -/
theorem scalarProfile_amplitude_sq_strict_lt_before_nonzero_endpoint_of_pos_viscosity
    (hν : 0 < ν) {a : NSTime → ℝ} (f : NSSchwartzInitialVelocity)
    (hvelocity : S.velocity = fun r y => a r • f y)
    {s t T : NSTime} (hst : s < t) (htT : t ≤ T)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    (a t) ^ (2 : ℕ) < (a s) ^ (2 : ℕ) :=
  SchwartzConcreteNavierStokesSolution.scalarProfile_amplitude_sq_strict_lt_before_nonzero_endpoint_of_pos_viscosity
      S.toSchwartzConcreteNavierStokesSolution hν f hvelocity hst htT hneT

/-- A positive-viscosity nonzero one-profile candidate has a nonzero endpoint
whose entire past support ray has strictly decreasing squared amplitude. -/
theorem exists_nonzero_endpoint_with_scalarProfile_amplitude_sq_strict_drop
    (hν : 0 < ν) {a : NSTime → ℝ} (f : NSSchwartzInitialVelocity)
    (hvelocity : S.velocity = fun r y => a r • f y) :
    ∃ T xT,
      S.velocity T xT ≠ 0 ∧
        ∀ {s t : NSTime}, s < t → t ≤ T →
          (a t) ^ (2 : ℕ) < (a s) ^ (2 : ℕ) := by
  rcases S.nonzero_velocity with ⟨T, xT, hneT⟩
  exact
    ⟨T, xT, hneT, fun {_s _t} hst htT =>
      S.scalarProfile_amplitude_sq_strict_lt_before_nonzero_endpoint_of_pos_viscosity
        hν f hvelocity hst htT ⟨xT, hneT⟩⟩

/-- Exact Stokes-flow specialization of the support kernel: the same
endpoint-parametric energy ordering holds while the Stokes subroute kernel is
available for the candidate generator. -/
theorem stokesFlow_nonzeroTimeSupport_packet
    (hν : 0 < ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      SchwartzNonzeroTimeSupportKernel ν S.velocity S.pressure ∧
      ∀ {s t T : NSTime}, s < t → t ≤ T →
        (∃ xT : NSSpace, S.velocity T xT ≠ 0) →
          normalizedKineticEnergy S.velocity t <
            normalizedKineticEnergy S.velocity s := by
  exact
    ⟨S.nonzeroStokesFlowKernel hconv hpressure,
      S.nonzeroTimeSupportKernel,
      fun {_s _t _T} hst htT hne =>
        S.normalizedKineticEnergy_strict_lt_before_nonzero_endpoint_of_pos_viscosity
          hν hst htT hne⟩

end NonzeroSchwartzConcreteNavierStokesSolution

/-- Global no-go form: before a later nonzero endpoint, a positive-viscosity
nonzero slice-Schwartz solution cannot have a nondecreasing normalized-energy
subinterval. -/
theorem
    not_exists_nonzeroSchwartzConcreteSolution_energy_nondecrease_before_nonzero_endpoint_of_pos_viscosity
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ s t T : NSTime,
        s < t ∧ t ≤ T ∧
          (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
            normalizedKineticEnergy S.velocity s ≤
              normalizedKineticEnergy S.velocity t := by
  rintro ⟨S, s, t, T, hst, htT, hneT, hnondec⟩
  have hdrop :
      normalizedKineticEnergy S.velocity t <
        normalizedKineticEnergy S.velocity s :=
    S.normalizedKineticEnergy_strict_lt_before_nonzero_endpoint_of_pos_viscosity
      hν hst htT hneT
  exact not_lt_of_ge hnondec hdrop

/-- Global one-profile amplitude no-recurrence obstruction: a positive-
viscosity nonzero slice-Schwartz solution represented by a fixed Schwartz
profile cannot have nondecreasing squared amplitude on any nontrivial forward
interval before a later nonzero endpoint. -/
theorem
    not_exists_nonzeroSchwartzConcreteSolution_scalarProfile_amplitude_sq_nondecrease_before_nonzero_endpoint_of_pos_viscosity
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity),
        S.velocity = (fun r y => a r • f y) ∧
          ∃ s t T : NSTime,
            s < t ∧ t ≤ T ∧
              (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
                (a s) ^ (2 : ℕ) ≤ (a t) ^ (2 : ℕ) := by
  rintro ⟨S, a, f, hvelocity, s, t, T, hst, htT, hneT, hnondec⟩
  have hdrop :
      (a t) ^ (2 : ℕ) < (a s) ^ (2 : ℕ) :=
    S.scalarProfile_amplitude_sq_strict_lt_before_nonzero_endpoint_of_pos_viscosity
      hν f hvelocity hst htT hneT
  exact not_lt_of_ge hnondec hdrop

end NavierStokes
end FluidDynamics
end Mettapedia
