import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzZeroRestartObstruction

/-!
# Slice-Schwartz Past-Dissipation Ray

This module combines the zero-restart obstruction with the strict
positive-viscosity energy identity.  A later nonzero witness forces every
earlier slice to be nonzero somewhere; at positive viscosity, every such slice
then has strictly positive corrected dissipation and a strictly negative
normalized-energy derivative.  Consequently, before that witness time the
normalized kinetic energy is strictly decreasing along every nontrivial forward
time interval.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap Topology

namespace NonzeroSchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)

/-- A positive-viscosity nonzero solution has a nonzero witness whose entire
past is strictly dissipative in the exact coordinate energy identity. -/
theorem exists_nonzero_witness_with_strict_dissipation_at_all_prior_times
    (hν : 0 < ν) :
    ∃ t₁ x₁,
      S.velocity t₁ x₁ ≠ 0 ∧
        ∀ t₀ : NSTime, t₀ ≤ t₁ →
          (∃ x₀ : NSSpace, S.velocity t₀ x₀ ≠ 0) ∧
            0 < coordinateEnergyDissipationRate S.velocity ν t₀ ∧
            HasDerivAt (normalizedKineticEnergy S.velocity)
              (-(coordinateEnergyDissipationRate S.velocity ν t₀)) t₀ ∧
            -(coordinateEnergyDissipationRate S.velocity ν t₀) < 0 := by
  rcases
      S.exists_nonzero_witness_with_nonzero_at_all_prior_times hν.le with
    ⟨t₁, x₁, hne₁, hpast⟩
  refine ⟨t₁, x₁, hne₁, ?_⟩
  intro t₀ ht
  have hne₀ : ∃ x₀ : NSSpace, S.velocity t₀ x₀ ≠ 0 := hpast t₀ ht
  have hrate :
      0 < coordinateEnergyDissipationRate S.velocity ν t₀ :=
    SchwartzConcreteNavierStokesSolution.coordinateEnergyDissipationRate_pos_of_exists_velocity_ne_zero
      S.toSchwartzConcreteNavierStokesSolution hν hne₀
  exact
    ⟨hne₀, hrate,
      S.coordinateEnergyDissipationIdentity t₀,
      neg_neg_of_pos hrate⟩

/-- A positive-viscosity nonzero solution has a nonzero witness such that
normalized kinetic energy is strictly decreasing on every earlier nontrivial
forward interval ending no later than that witness. -/
theorem exists_nonzero_witness_with_strict_past_energy_drop
    (hν : 0 < ν) :
    ∃ t₁ x₁,
      S.velocity t₁ x₁ ≠ 0 ∧
        ∀ s t : NSTime, s < t → t ≤ t₁ →
          normalizedKineticEnergy S.velocity t <
            normalizedKineticEnergy S.velocity s := by
  rcases S.nonzero_velocity with ⟨t₁, x₁, hne₁⟩
  refine ⟨t₁, x₁, hne₁, ?_⟩
  intro s t hst ht
  have hs_le_t₁ : s ≤ t₁ := le_trans (le_of_lt hst) ht
  rcases
      S.exists_velocity_ne_zero_at_or_before_nonzero_of_nonneg_viscosity
        hν.le hs_le_t₁ hne₁ with
    ⟨xs, hnes⟩
  exact
    S.normalizedKineticEnergy_strict_lt_after_nonzero_of_pos_viscosity
      hν hnes hst

/-- Exact Stokes-flow specialization of the past-dissipation ray: an inhabited
positive-viscosity Stokes candidate must carry the Stokes kernel and a whole
past half-line of strict dissipation before some nonzero witness. -/
theorem stokesFlow_past_strictDissipation_packet
    (hν : 0 < ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      ∃ t₁ x₁,
        S.velocity t₁ x₁ ≠ 0 ∧
          ∀ t₀ : NSTime, t₀ ≤ t₁ →
            (∃ x₀ : NSSpace, S.velocity t₀ x₀ ≠ 0) ∧
              0 < coordinateEnergyDissipationRate S.velocity ν t₀ ∧
              HasDerivAt (normalizedKineticEnergy S.velocity)
                (-(coordinateEnergyDissipationRate S.velocity ν t₀)) t₀ ∧
              -(coordinateEnergyDissipationRate S.velocity ν t₀) < 0 := by
  exact
    ⟨S.nonzeroStokesFlowKernel hconv hpressure,
      S.exists_nonzero_witness_with_strict_dissipation_at_all_prior_times hν⟩

end NonzeroSchwartzConcreteNavierStokesSolution

end NavierStokes
end FluidDynamics
end Mettapedia
