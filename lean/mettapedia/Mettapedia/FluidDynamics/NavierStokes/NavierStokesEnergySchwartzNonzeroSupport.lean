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

end NavierStokes
end FluidDynamics
end Mettapedia
