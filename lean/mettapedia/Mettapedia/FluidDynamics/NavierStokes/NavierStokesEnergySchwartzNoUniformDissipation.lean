import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzNonzeroSupport

/-!
# No Uniform Past Dissipation for Slice-Schwartz Solutions

This module extracts a quantitative obstruction from the bounded whole-time
energy assumption in the concrete slice-Schwartz Navier-Stokes interface.  A
bounded eternal solution cannot keep the corrected coordinate dissipation rate
uniformly above a positive constant on an entire past ray.  Consequently, if a
positive-viscosity solution has a later nonzero endpoint, then every positive
dissipation threshold is crossed at some earlier nonzero slice.

This sharpens the exact nonzero-canary search: a bounded whole-time Stokes or
pressure-closure candidate cannot be certified by a uniform past spectral-gap
lower bound.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open Set
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap Topology

namespace SchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν)

/-- Any nonzero value in a Schwartz velocity slice gives strictly positive
normalized kinetic energy at that time. -/
theorem normalizedKineticEnergy_pos_of_velocity_ne_zero
    {t : NSTime} {x : NSSpace} (hne : S.velocity t x ≠ 0) :
    0 < normalizedKineticEnergy S.velocity t := by
  have hkin_nonneg : 0 ≤ kineticEnergyAt S.velocity t :=
    kineticEnergyAt_nonneg S.velocity t
  have hkin_ne : kineticEnergyAt S.velocity t ≠ 0 := by
    intro hzero
    have hvelzero :
        S.velocity t x = 0 :=
      S.velocity_eq_zero_of_kineticEnergyAt_eq_zero hzero x
    exact hne hvelzero
  have hkin_pos : 0 < kineticEnergyAt S.velocity t :=
    lt_of_le_of_ne hkin_nonneg (Ne.symm hkin_ne)
  rw [normalizedKineticEnergy]
  nlinarith

/-- Existential form of positive normalized kinetic energy on a nonzero
Schwartz velocity slice. -/
theorem normalizedKineticEnergy_pos_of_exists_velocity_ne_zero
    {t : NSTime} (hne : ∃ x : NSSpace, S.velocity t x ≠ 0) :
    0 < normalizedKineticEnergy S.velocity t := by
  rcases hne with ⟨x, hx⟩
  exact S.normalizedKineticEnergy_pos_of_velocity_ne_zero hx

/-- A bounded whole-time slice-Schwartz concrete solution cannot keep its
corrected dissipation rate uniformly above a positive constant on a whole past
ray. -/
theorem not_forall_past_coordinateEnergyDissipationRate_ge
    {κ T : NSTime} (hκ : 0 < κ) :
    ¬ ∀ t : NSTime, t ≤ T →
      κ ≤ coordinateEnergyDissipationRate S.velocity ν t := by
  intro hgap
  rcases S.bounded_energy with ⟨C, hC, hbound⟩
  let s : NSTime := T - (C + 1) / κ
  let E : NSTime → ℝ := normalizedKineticEnergy S.velocity
  have hC1 : 0 < C + 1 := by linarith
  have hsT : s ≤ T := by
    have hdiv : 0 < (C + 1) / κ := div_pos hC1 hκ
    dsimp [s]
    linarith
  have hcont : ContinuousOn E (Icc s T) := by
    intro x _hx
    exact (S.coordinateEnergyDissipationIdentity x).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ E (interior (Icc s T)) := by
    intro x _hx
    exact (S.coordinateEnergyDissipationIdentity x).differentiableAt.differentiableWithinAt
  have hderiv_le :
      ∀ x ∈ interior (Icc s T), deriv E x ≤ -κ := by
    intro x hx
    have hxIcc : x ∈ Icc s T := interior_subset hx
    have hrate :
        κ ≤ coordinateEnergyDissipationRate S.velocity ν x :=
      hgap x hxIcc.2
    have hderiv :
        deriv E x = -(coordinateEnergyDissipationRate S.velocity ν x) := by
      dsimp [E]
      exact (S.coordinateEnergyDissipationIdentity x).deriv
    rw [hderiv]
    exact neg_le_neg hrate
  have hmv :
      E T - E s ≤ -κ * (T - s) :=
    (convex_Icc s T).image_sub_le_mul_sub_of_deriv_le
      hcont hdiff hderiv_le
      s (left_mem_Icc.mpr hsT) T (right_mem_Icc.mpr hsT) hsT
  have hgrowth : κ * (T - s) ≤ E s - E T := by
    nlinarith
  have hspan : κ * (T - s) = C + 1 := by
    calc
      κ * (T - s) = κ * ((C + 1) / κ) := by
        congr 1
        dsimp [s]
        ring
      _ = C + 1 := by
        field_simp [ne_of_gt hκ]
  have hlower : C + 1 ≤ E s - E T := by
    simpa [hspan] using hgrowth
  have hE_s_le_C : E s ≤ C := by
    have hkin_le_C : kineticEnergyAt S.velocity s ≤ C := (hbound s).2
    have hkin_nonneg : 0 ≤ kineticEnergyAt S.velocity s :=
      kineticEnergyAt_nonneg S.velocity s
    dsimp [E]
    rw [normalizedKineticEnergy]
    nlinarith
  have hE_T_nonneg : 0 ≤ E T := by
    dsimp [E]
    exact normalizedKineticEnergy_nonneg S.velocity T
  have hupper : E s - E T ≤ C := by
    linarith
  have : C + 1 ≤ C := le_trans hlower hupper
  linarith

/-- Positive form of the no-uniform-gap theorem: below every positive
threshold, some time on the past ray has corrected dissipation below that
threshold. -/
theorem exists_past_coordinateEnergyDissipationRate_lt
    {κ T : NSTime} (hκ : 0 < κ) :
    ∃ t : NSTime,
      t ≤ T ∧ coordinateEnergyDissipationRate S.velocity ν t < κ := by
  by_contra hnone
  have hall :
      ∀ t : NSTime, t ≤ T →
        κ ≤ coordinateEnergyDissipationRate S.velocity ν t := by
    intro t ht
    exact le_of_not_gt fun hlt => hnone ⟨t, ht, hlt⟩
  exact (S.not_forall_past_coordinateEnergyDissipationRate_ge hκ) hall

/-- Endpoint version: if a positive-viscosity solution is nonzero at a later
endpoint, then every positive threshold is crossed at some earlier nonzero slice
with strictly positive but smaller corrected dissipation. -/
theorem exists_past_nonzero_with_small_positive_coordinateEnergyDissipationRate
    (hν : 0 < ν) {κ T : NSTime}
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) (hκ : 0 < κ) :
    ∃ t : NSTime,
      t ≤ T ∧
        (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
          0 < coordinateEnergyDissipationRate S.velocity ν t ∧
            coordinateEnergyDissipationRate S.velocity ν t < κ := by
  rcases S.exists_past_coordinateEnergyDissipationRate_lt (ν := ν) (κ := κ) (T := T) hκ with
    ⟨t, htT, hlt⟩
  have hne :
      ∃ x : NSSpace, S.velocity t x ≠ 0 :=
    S.exists_velocity_ne_zero_at_or_before_nonzero_endpoint_of_nonneg_viscosity
      hν.le htT hneT
  have hpos :
      0 < coordinateEnergyDissipationRate S.velocity ν t :=
    S.coordinateEnergyDissipationRate_pos_of_exists_velocity_ne_zero hν hne
  exact ⟨t, htT, hne, hpos, hlt⟩

/-- A positive whole-past spectral/Poincare floor is impossible before any
nonzero endpoint.  The floor would turn the positive endpoint energy into a
uniform positive corrected-dissipation gap on the whole past ray. -/
theorem not_forall_past_coordinateEnergyDissipationRate_ge_mul_normalizedKineticEnergy
    (hν : 0 ≤ ν) {lam T : NSTime} (hlam : 0 < lam)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    ¬ ∀ t : NSTime, t ≤ T →
      lam * normalizedKineticEnergy S.velocity t ≤
        coordinateEnergyDissipationRate S.velocity ν t := by
  have hET :
      0 < normalizedKineticEnergy S.velocity T :=
    S.normalizedKineticEnergy_pos_of_exists_velocity_ne_zero hneT
  let κ : NSTime := lam * normalizedKineticEnergy S.velocity T
  have hκ : 0 < κ := by
    dsimp [κ]
    exact mul_pos hlam hET
  intro hfloor
  have hgap :
      ∀ t : NSTime, t ≤ T →
        κ ≤ coordinateEnergyDissipationRate S.velocity ν t := by
    intro t ht
    have henergy :
        normalizedKineticEnergy S.velocity T ≤
          normalizedKineticEnergy S.velocity t :=
      S.normalizedKineticEnergy_antitone hν ht
    have hmul :
        lam * normalizedKineticEnergy S.velocity T ≤
          lam * normalizedKineticEnergy S.velocity t :=
      mul_le_mul_of_nonneg_left henergy hlam.le
    exact le_trans hmul (hfloor t ht)
  exact (S.not_forall_past_coordinateEnergyDissipationRate_ge hκ) hgap

/-- Positive witness form of the past spectral-floor obstruction: before any
nonzero endpoint of a positive-viscosity solution, every positive candidate
Rayleigh coefficient is beaten by an earlier nonzero slice with positive
dissipation. -/
theorem exists_past_nonzero_with_small_positive_dissipation_per_energy
    (hν : 0 < ν) {lam T : NSTime}
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) (hlam : 0 < lam) :
    ∃ t : NSTime,
      t ≤ T ∧
        (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
          0 < coordinateEnergyDissipationRate S.velocity ν t ∧
            coordinateEnergyDissipationRate S.velocity ν t <
              lam * normalizedKineticEnergy S.velocity t := by
  by_contra hnone
  have hfloor :
      ∀ t : NSTime, t ≤ T →
        lam * normalizedKineticEnergy S.velocity t ≤
          coordinateEnergyDissipationRate S.velocity ν t := by
    intro t ht
    have hne :
        ∃ x : NSSpace, S.velocity t x ≠ 0 :=
      S.exists_velocity_ne_zero_at_or_before_nonzero_endpoint_of_nonneg_viscosity
        hν.le ht hneT
    have hpos :
        0 < coordinateEnergyDissipationRate S.velocity ν t :=
      S.coordinateEnergyDissipationRate_pos_of_exists_velocity_ne_zero hν hne
    exact le_of_not_gt fun hlt => hnone ⟨t, ht, hne, hpos, hlt⟩
  exact
    (S.not_forall_past_coordinateEnergyDissipationRate_ge_mul_normalizedKineticEnergy
      hν.le hlam hneT) hfloor

end SchwartzConcreteNavierStokesSolution

namespace NonzeroSchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)

/-- A positive-viscosity nonzero solution has a nonzero endpoint whose whole
past ray has arbitrarily small positive corrected dissipation samples. -/
theorem exists_nonzero_endpoint_with_arbitrarily_small_past_dissipation
    (hν : 0 < ν) :
    ∃ T xT,
      S.velocity T xT ≠ 0 ∧
        ∀ κ : NSTime, 0 < κ →
          ∃ t : NSTime,
            t ≤ T ∧
              (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
                0 < coordinateEnergyDissipationRate S.velocity ν t ∧
                  coordinateEnergyDissipationRate S.velocity ν t < κ := by
  rcases S.nonzero_velocity with ⟨T, xT, hneT⟩
  refine ⟨T, xT, hneT, ?_⟩
  intro κ hκ
  exact
    S.toSchwartzConcreteNavierStokesSolution
      |>.exists_past_nonzero_with_small_positive_coordinateEnergyDissipationRate
        hν ⟨xT, hneT⟩ hκ

/-- Exact Stokes-flow specialization of the quantitative obstruction: a
positive-viscosity nonzero Stokes candidate carries the Stokes kernel, but its
past dissipation cannot be uniformly bounded below by any positive constant. -/
theorem stokesFlow_noUniformPastDissipation_packet
    (hν : 0 < ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      ∃ T xT,
        S.velocity T xT ≠ 0 ∧
          ∀ κ : NSTime, 0 < κ →
            ∃ t : NSTime,
              t ≤ T ∧
                (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
                  0 < coordinateEnergyDissipationRate S.velocity ν t ∧
                    coordinateEnergyDissipationRate S.velocity ν t < κ := by
  exact
    ⟨S.nonzeroStokesFlowKernel hconv hpressure,
      S.exists_nonzero_endpoint_with_arbitrarily_small_past_dissipation hν⟩

/-- A positive-viscosity nonzero solution has a nonzero endpoint whose whole
past ray contains nonzero slices with arbitrarily small positive dissipation
relative to normalized kinetic energy. -/
theorem exists_nonzero_endpoint_with_arbitrarily_small_past_dissipation_per_energy
    (hν : 0 < ν) :
    ∃ T xT,
      S.velocity T xT ≠ 0 ∧
        ∀ lam : NSTime, 0 < lam →
          ∃ t : NSTime,
            t ≤ T ∧
              (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
                0 < coordinateEnergyDissipationRate S.velocity ν t ∧
                  coordinateEnergyDissipationRate S.velocity ν t <
                    lam * normalizedKineticEnergy S.velocity t := by
  rcases S.nonzero_velocity with ⟨T, xT, hneT⟩
  refine ⟨T, xT, hneT, ?_⟩
  intro lam hlam
  exact
    S.toSchwartzConcreteNavierStokesSolution
      |>.exists_past_nonzero_with_small_positive_dissipation_per_energy
        hν ⟨xT, hneT⟩ hlam

/-- Exact Stokes-flow specialization of the spectral-floor obstruction: no
positive-viscosity nonzero Stokes candidate can keep a positive Poincare-style
floor `lambda * energy <= dissipation` on the whole past ray of a nonzero
endpoint. -/
theorem stokesFlow_noPastSpectralFloor_packet
    (hν : 0 < ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {lam T : NSTime} (hlam : 0 < lam)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      ¬ ∀ t : NSTime, t ≤ T →
        lam * normalizedKineticEnergy S.velocity t ≤
          coordinateEnergyDissipationRate S.velocity ν t := by
  exact
    ⟨S.nonzeroStokesFlowKernel hconv hpressure,
      S.toSchwartzConcreteNavierStokesSolution
        |>.not_forall_past_coordinateEnergyDissipationRate_ge_mul_normalizedKineticEnergy
          hν.le hlam hneT⟩

/-- Exact Stokes-flow specialization of the positive witness form: a
positive-viscosity nonzero Stokes candidate cannot avoid arbitrarily small
positive dissipation-per-energy samples on the whole past ray of some nonzero
endpoint. -/
theorem stokesFlow_smallPastDissipationPerEnergy_packet
    (hν : 0 < ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      ∃ T xT,
        S.velocity T xT ≠ 0 ∧
          ∀ lam : NSTime, 0 < lam →
            ∃ t : NSTime,
              t ≤ T ∧
                (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
                  0 < coordinateEnergyDissipationRate S.velocity ν t ∧
                    coordinateEnergyDissipationRate S.velocity ν t <
                      lam * normalizedKineticEnergy S.velocity t := by
  exact
    ⟨S.nonzeroStokesFlowKernel hconv hpressure,
      S.exists_nonzero_endpoint_with_arbitrarily_small_past_dissipation_per_energy hν⟩

end NonzeroSchwartzConcreteNavierStokesSolution

/-- Global no-go form for uniform past dissipation gaps in the nonzero
slice-Schwartz interface. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_uniform_past_dissipation_gap
    {ν κ : ℝ} (hκ : 0 < κ) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ T : NSTime,
        ∀ t : NSTime, t ≤ T →
          κ ≤ coordinateEnergyDissipationRate S.velocity ν t := by
  rintro ⟨S, T, hgap⟩
  exact
    (S.toSchwartzConcreteNavierStokesSolution
      |>.not_forall_past_coordinateEnergyDissipationRate_ge hκ) hgap

/-- Global no-go form for positive Poincare-style past spectral floors in the
nonzero slice-Schwartz interface. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_past_spectral_floor
    {ν lam : ℝ} (hν : 0 ≤ ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ T : NSTime,
        (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
          ∀ t : NSTime, t ≤ T →
            lam * normalizedKineticEnergy S.velocity t ≤
              coordinateEnergyDissipationRate S.velocity ν t := by
  rintro ⟨S, T, hneT, hfloor⟩
  exact
    (S.toSchwartzConcreteNavierStokesSolution
      |>.not_forall_past_coordinateEnergyDissipationRate_ge_mul_normalizedKineticEnergy
        hν hlam hneT) hfloor

end NavierStokes
end FluidDynamics
end Mettapedia
