import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzStokesKernel

/-!
# Slice-Schwartz Zero-Restart Obstruction

This module factors a basic no-restart consequence of the concrete
slice-Schwartz energy identity.  A zero velocity slice has zero kinetic energy;
nonnegative viscosity makes kinetic energy nonincreasing; and zero kinetic
energy on a Schwartz slice forces the velocity slice itself to vanish.  Hence a
candidate cannot pass from a zero slice to a later nonzero slice inside the
current concrete solution interface.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap Topology

/-- Reusable no-restart kernel extracted from a concrete slice-Schwartz
solution. -/
structure SchwartzZeroRestartKernel
    (ν : ℝ) (u : NSVelocityField) (p : NSPressureField) where
  concrete : SchwartzConcreteSolutionKernel ν u p
  kineticZeroRigidity :
    ∀ t, kineticEnergyAt u t = 0 → ∀ x, u t x = 0
  noFutureRestart :
    0 ≤ ν → ∀ {t₀ t₁ : NSTime}, t₀ ≤ t₁ →
      (∀ x, u t₀ x = 0) → ∀ x, u t₁ x = 0

namespace SchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν)

/-- A pointwise-zero velocity slice has zero kinetic energy. -/
theorem kineticEnergyAt_eq_zero_of_velocity_eq_zero_at
    {t : NSTime} (hzero : ∀ x, S.velocity t x = 0) :
    kineticEnergyAt S.velocity t = 0 := by
  simp [kineticEnergyAt, kineticEnergyDensity, hzero]

/-- Zero kinetic energy on a Schwartz velocity slice forces that slice to
vanish pointwise. -/
theorem velocity_eq_zero_of_kineticEnergyAt_eq_zero
    {t : NSTime} (henergy : kineticEnergyAt S.velocity t = 0) :
    ∀ x, S.velocity t x = 0 := by
  intro x
  let f : 𝓢(NSSpace, NSSpace) := S.velocitySlice t
  let g : NSSpace → ℝ := fun y => ‖f y‖ ^ (2 : ℕ)
  have hsliceFun : (fun y : NSSpace => S.velocity t y) = (f : NSSpace → NSSpace) := by
    funext y
    exact S.velocitySlice_eq t y
  have hdensity : kineticEnergyDensity S.velocity t = g := by
    funext y
    simp [kineticEnergyDensity, g, hsliceFun]
  have hgint : Integrable g := by
    exact integrable_norm_sq_of_schwartz f
  have hgcont : Continuous g := by
    exact f.continuous.norm.pow 2
  have hgnonneg : 0 ≤ g := by
    intro y
    positivity
  have hgintegral : ∫ y, g y ∂volume = 0 := by
    simpa [kineticEnergyAt, hdensity] using henergy
  by_contra hne
  have hfne : f x ≠ 0 := by
    intro hfx
    have hvel : S.velocity t x = 0 := by
      simpa [f, hfx] using S.velocitySlice_eq t x
    exact hne hvel
  have hgx_ne : g x ≠ 0 := by
    simp [g, hfne]
  have hpos : 0 < ∫ y, g y ∂volume :=
    MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
      (x := x) hgcont hgint hgnonneg hgx_ne
  rw [hgintegral] at hpos
  exact lt_irrefl 0 hpos

/-- At nonnegative viscosity, a zero velocity slice cannot be followed by a
later nonzero slice. -/
theorem velocity_eq_zero_at_later_of_velocity_eq_zero_at_of_nonneg_viscosity
    (hν : 0 ≤ ν) {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁)
    (hzero : ∀ x, S.velocity t₀ x = 0) :
    ∀ x, S.velocity t₁ x = 0 := by
  have henergy₀ : kineticEnergyAt S.velocity t₀ = 0 :=
    S.kineticEnergyAt_eq_zero_of_velocity_eq_zero_at hzero
  have hle : kineticEnergyAt S.velocity t₁ ≤ kineticEnergyAt S.velocity t₀ :=
    S.kineticEnergyAt_le_of_le hν ht
  have henergy₁ : kineticEnergyAt S.velocity t₁ = 0 := by
    exact le_antisymm (by simpa [henergy₀] using hle) (kineticEnergyAt_nonneg S.velocity t₁)
  exact S.velocity_eq_zero_of_kineticEnergyAt_eq_zero henergy₁

/-- The reusable no-restart kernel carried by any nonnegative-viscosity
slice-Schwartz concrete solution. -/
def zeroRestartKernel :
    SchwartzZeroRestartKernel ν S.velocity S.pressure where
  concrete := S.concreteSolutionKernel
  kineticZeroRigidity := fun t henergy =>
    S.velocity_eq_zero_of_kineticEnergyAt_eq_zero (t := t) henergy
  noFutureRestart := fun hν {_t₀ _t₁} ht hzero =>
    S.velocity_eq_zero_at_later_of_velocity_eq_zero_at_of_nonneg_viscosity hν ht hzero

end SchwartzConcreteNavierStokesSolution

namespace NonzeroSchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)

/-- Nonzero solutions inherit the no-restart kernel. -/
def zeroRestartKernel :
    SchwartzZeroRestartKernel ν S.velocity S.pressure :=
  S.toSchwartzConcreteNavierStokesSolution.zeroRestartKernel

/-- Nonzero-interface no-restart form: if a slice is zero, no later slice can
contain a nonzero value. -/
theorem not_velocity_ne_zero_at_or_after_zero_slice_of_nonneg_viscosity
    (hν : 0 ≤ ν) {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁)
    (hzero : ∀ x, S.velocity t₀ x = 0) (x : NSSpace) :
    ¬ S.velocity t₁ x ≠ 0 := by
  intro hne
  have hzero₁ :
      S.velocity t₁ x = 0 :=
    SchwartzConcreteNavierStokesSolution.velocity_eq_zero_at_later_of_velocity_eq_zero_at_of_nonneg_viscosity
      S.toSchwartzConcreteNavierStokesSolution hν ht hzero x
  exact hne hzero₁

/-- Stokes-flow specialization of the no-restart gate.  The Stokes hypotheses
are kept in the statement so zero-pressure/zero-convection candidate searches
can call this theorem directly. -/
theorem stokesFlow_not_velocity_ne_zero_at_or_after_zero_slice_of_nonneg_viscosity
    (hν : 0 ≤ ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁)
    (hzero : ∀ x, S.velocity t₀ x = 0) (x : NSSpace) :
    ¬ S.velocity t₁ x ≠ 0 := by
  have _kernel : NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure :=
    S.nonzeroStokesFlowKernel hconv hpressure
  exact S.not_velocity_ne_zero_at_or_after_zero_slice_of_nonneg_viscosity
    hν ht hzero x

end NonzeroSchwartzConcreteNavierStokesSolution

/-- Global Stokes-flow no-restart obstruction: a nonnegative-viscosity nonzero
Stokes-flow candidate cannot have a zero slice before a later nonzero value. -/
theorem not_exists_nonzeroSchwartzStokesFlow_zero_slice_before_nonzero_of_nonneg_viscosity
    {ν : ℝ} (hν : 0 ≤ ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      (∀ t x, spatialConvection S.velocity t x = 0) ∧
        (∀ t x, spatialPressureGradient S.pressure t x = 0) ∧
        ∃ t₀ t₁ : NSTime,
          t₀ ≤ t₁ ∧
            (∀ x, S.velocity t₀ x = 0) ∧
            ∃ x, S.velocity t₁ x ≠ 0 := by
  rintro ⟨S, hconv, hpressure, t₀, t₁, ht, hzero, x, hne⟩
  exact
    S.stokesFlow_not_velocity_ne_zero_at_or_after_zero_slice_of_nonneg_viscosity
      hν hconv hpressure ht hzero x hne

end NavierStokes
end FluidDynamics
end Mettapedia
