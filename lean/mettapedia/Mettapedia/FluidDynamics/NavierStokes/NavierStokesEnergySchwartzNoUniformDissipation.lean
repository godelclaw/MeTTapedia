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

/-- A nonnegative energy identity also forbids a uniform positive corrected
dissipation rate on an entire future ray.  Otherwise the normalized kinetic
energy would become negative after a sufficiently long interval. -/
theorem not_forall_future_coordinateEnergyDissipationRate_ge
    {κ T : NSTime} (hκ : 0 < κ) :
    ¬ ∀ t : NSTime, T ≤ t →
      κ ≤ coordinateEnergyDissipationRate S.velocity ν t := by
  intro hgap
  let E : NSTime → ℝ := normalizedKineticEnergy S.velocity
  let R : NSTime := T + (E T + 1) / κ
  have hET_nonneg : 0 ≤ E T := by
    dsimp [E]
    exact normalizedKineticEnergy_nonneg S.velocity T
  have hET1 : 0 < E T + 1 := by
    linarith
  have hTR : T ≤ R := by
    have hdiv : 0 < (E T + 1) / κ := div_pos hET1 hκ
    dsimp [R]
    linarith
  have hcont : ContinuousOn E (Icc T R) := by
    intro x _hx
    exact (S.coordinateEnergyDissipationIdentity x).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ E (interior (Icc T R)) := by
    intro x _hx
    exact (S.coordinateEnergyDissipationIdentity x).differentiableAt.differentiableWithinAt
  have hderiv_le :
      ∀ x ∈ interior (Icc T R), deriv E x ≤ -κ := by
    intro x hx
    have hxIcc : x ∈ Icc T R := interior_subset hx
    have hrate :
        κ ≤ coordinateEnergyDissipationRate S.velocity ν x :=
      hgap x hxIcc.1
    have hderiv :
        deriv E x = -(coordinateEnergyDissipationRate S.velocity ν x) := by
      dsimp [E]
      exact (S.coordinateEnergyDissipationIdentity x).deriv
    rw [hderiv]
    exact neg_le_neg hrate
  have hmv :
      E R - E T ≤ -κ * (R - T) :=
    (convex_Icc T R).image_sub_le_mul_sub_of_deriv_le
      hcont hdiff hderiv_le
      T (left_mem_Icc.mpr hTR) R (right_mem_Icc.mpr hTR) hTR
  have hspan : κ * (R - T) = E T + 1 := by
    calc
      κ * (R - T) = κ * ((E T + 1) / κ) := by
        congr 1
        dsimp [R]
        ring
      _ = E T + 1 := by
        field_simp [ne_of_gt hκ]
  have hnegative : E R < 0 := by
    nlinarith
  have hnonneg : 0 ≤ E R := by
    dsimp [E]
    exact normalizedKineticEnergy_nonneg S.velocity R
  exact not_lt_of_ge hnonneg hnegative

/-- Positive form of the future no-uniform-gap theorem: every positive
threshold is beaten at some time on every future ray. -/
theorem exists_future_coordinateEnergyDissipationRate_lt
    {κ T : NSTime} (hκ : 0 < κ) :
    ∃ t : NSTime,
      T ≤ t ∧ coordinateEnergyDissipationRate S.velocity ν t < κ := by
  by_contra hnone
  have hall :
      ∀ t : NSTime, T ≤ t →
        κ ≤ coordinateEnergyDissipationRate S.velocity ν t := by
    intro t ht
    exact le_of_not_gt fun hlt => hnone ⟨t, ht, hlt⟩
  exact (S.not_forall_future_coordinateEnergyDissipationRate_ge hκ) hall

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

/-- Rayleigh-quotient form of the past spectral-floor obstruction: the
corrected dissipation divided by normalized kinetic energy is positive but
arbitrarily small somewhere on the past ray before any nonzero endpoint. -/
theorem exists_past_nonzero_with_small_positive_dissipation_ratio
    (hν : 0 < ν) {lam T : NSTime}
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) (hlam : 0 < lam) :
    ∃ t : NSTime,
      t ≤ T ∧
        (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
          0 < coordinateEnergyDissipationRate S.velocity ν t ∧
            0 < normalizedKineticEnergy S.velocity t ∧
              0 <
                coordinateEnergyDissipationRate S.velocity ν t /
                  normalizedKineticEnergy S.velocity t ∧
                coordinateEnergyDissipationRate S.velocity ν t /
                    normalizedKineticEnergy S.velocity t < lam := by
  rcases S.exists_past_nonzero_with_small_positive_dissipation_per_energy
      hν hneT hlam with
    ⟨t, htT, hne, hDpos, hlt⟩
  have hEpos :
      0 < normalizedKineticEnergy S.velocity t :=
    S.normalizedKineticEnergy_pos_of_exists_velocity_ne_zero hne
  have hratio_pos :
      0 <
        coordinateEnergyDissipationRate S.velocity ν t /
          normalizedKineticEnergy S.velocity t :=
    div_pos hDpos hEpos
  have hratio_lt :
      coordinateEnergyDissipationRate S.velocity ν t /
          normalizedKineticEnergy S.velocity t < lam := by
    exact (div_lt_iff₀ hEpos).2 hlt
  exact ⟨t, htT, hne, hDpos, hEpos, hratio_pos, hratio_lt⟩

/-- Spatial Rayleigh-floor form of the past obstruction: before any nonzero
endpoint of a positive-viscosity solution, no positive lower bound of
coordinate enstrophy by normalized kinetic energy can hold on the whole past
ray.  This is the Poincare/eigenprofile obstruction stated at the spatial
profile level rather than through the viscosity-scaled dissipation rate. -/
theorem not_forall_past_coordinateEnstrophyAt_ge_mul_normalizedKineticEnergy
    (hν : 0 < ν) {lam T : NSTime} (hlam : 0 < lam)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    ¬ ∀ t : NSTime, t ≤ T →
      lam * normalizedKineticEnergy S.velocity t ≤
        coordinateEnstrophyAt S.velocity t := by
  intro hfloor
  have hscaled :
      ∀ t : NSTime, t ≤ T →
        (ν * lam) * normalizedKineticEnergy S.velocity t ≤
          coordinateEnergyDissipationRate S.velocity ν t := by
    intro t ht
    have hmul :
        ν * (lam * normalizedKineticEnergy S.velocity t) ≤
          ν * coordinateEnstrophyAt S.velocity t :=
      mul_le_mul_of_nonneg_left (hfloor t ht) hν.le
    simpa [coordinateEnergyDissipationRate, mul_assoc, mul_left_comm, mul_comm] using hmul
  exact
    (S.not_forall_past_coordinateEnergyDissipationRate_ge_mul_normalizedKineticEnergy
      hν.le (mul_pos hν hlam) hneT) hscaled

/-- Positive spatial Rayleigh-quotient form: before any nonzero endpoint of a
positive-viscosity solution, every positive spatial Poincare coefficient is
beaten by an earlier nonzero slice whose coordinate enstrophy divided by
normalized kinetic energy is positive but smaller than that coefficient. -/
theorem exists_past_nonzero_with_small_positive_coordinateEnstrophy_ratio
    (hν : 0 < ν) {lam T : NSTime}
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) (hlam : 0 < lam) :
    ∃ t : NSTime,
      t ≤ T ∧
        (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
          0 < coordinateEnstrophyAt S.velocity t ∧
            0 < normalizedKineticEnergy S.velocity t ∧
              0 <
                coordinateEnstrophyAt S.velocity t /
                  normalizedKineticEnergy S.velocity t ∧
                coordinateEnstrophyAt S.velocity t /
                    normalizedKineticEnergy S.velocity t < lam := by
  rcases S.exists_past_nonzero_with_small_positive_dissipation_ratio
      hν hneT (mul_pos hν hlam) with
    ⟨t, htT, hne, hDpos, hEpos, _hDratio_pos, hDratio_lt⟩
  have hEnst_pos :
      0 < coordinateEnstrophyAt S.velocity t := by
    have hmul :
        0 < ν * coordinateEnstrophyAt S.velocity t := by
      simpa [coordinateEnergyDissipationRate] using hDpos
    by_contra hnot
    have hnonpos : coordinateEnstrophyAt S.velocity t ≤ 0 := le_of_not_gt hnot
    have hle : ν * coordinateEnstrophyAt S.velocity t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hν.le hnonpos
    exact not_le_of_gt hmul hle
  have hratio_pos :
      0 <
        coordinateEnstrophyAt S.velocity t /
          normalizedKineticEnergy S.velocity t :=
    div_pos hEnst_pos hEpos
  have hscaled_ratio :
      ν *
          (coordinateEnstrophyAt S.velocity t /
            normalizedKineticEnergy S.velocity t) =
        coordinateEnergyDissipationRate S.velocity ν t /
          normalizedKineticEnergy S.velocity t := by
    rw [coordinateEnergyDissipationRate]
    ring
  have hratio_lt :
      coordinateEnstrophyAt S.velocity t /
          normalizedKineticEnergy S.velocity t < lam := by
    have hmul_lt :
        ν *
            (coordinateEnstrophyAt S.velocity t /
              normalizedKineticEnergy S.velocity t) <
          ν * lam := by
      simpa [hscaled_ratio] using hDratio_lt
    by_contra hnot
    have hle_ratio :
        lam ≤
          coordinateEnstrophyAt S.velocity t /
            normalizedKineticEnergy S.velocity t :=
      le_of_not_gt hnot
    have hle_mul :
        ν * lam ≤
          ν *
            (coordinateEnstrophyAt S.velocity t /
              normalizedKineticEnergy S.velocity t) :=
      mul_le_mul_of_nonneg_left hle_ratio hν.le
    exact not_le_of_gt hmul_lt hle_mul
  exact ⟨t, htT, hne, hEnst_pos, hEpos, hratio_pos, hratio_lt⟩

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

/-- Exact Stokes-flow specialization of the future no-uniform-gap theorem:
no positive dissipation threshold can hold forever to the future. -/
theorem stokesFlow_noUniformFutureDissipation_packet
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {κ T : NSTime} (hκ : 0 < κ) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      ∃ t : NSTime,
        T ≤ t ∧ coordinateEnergyDissipationRate S.velocity ν t < κ := by
  exact
    ⟨S.nonzeroStokesFlowKernel hconv hpressure,
      S.toSchwartzConcreteNavierStokesSolution
        |>.exists_future_coordinateEnergyDissipationRate_lt hκ⟩

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

/-- Quotient form: a positive-viscosity nonzero solution has a nonzero endpoint
whose whole past ray contains nonzero slices where the corrected
dissipation-to-normalized-energy ratio is positive but arbitrarily small. -/
theorem exists_nonzero_endpoint_with_arbitrarily_small_past_dissipation_ratio
    (hν : 0 < ν) :
    ∃ T xT,
      S.velocity T xT ≠ 0 ∧
        ∀ lam : NSTime, 0 < lam →
          ∃ t : NSTime,
            t ≤ T ∧
              (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
                0 < coordinateEnergyDissipationRate S.velocity ν t ∧
                  0 < normalizedKineticEnergy S.velocity t ∧
                    0 <
                      coordinateEnergyDissipationRate S.velocity ν t /
                        normalizedKineticEnergy S.velocity t ∧
                      coordinateEnergyDissipationRate S.velocity ν t /
                          normalizedKineticEnergy S.velocity t < lam := by
  rcases S.nonzero_velocity with ⟨T, xT, hneT⟩
  refine ⟨T, xT, hneT, ?_⟩
  intro lam hlam
  exact
    S.toSchwartzConcreteNavierStokesSolution
      |>.exists_past_nonzero_with_small_positive_dissipation_ratio
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

/-- Exact Stokes-flow specialization of the quotient form: a
positive-viscosity nonzero Stokes candidate has arbitrarily small positive
past corrected-dissipation Rayleigh quotients. -/
theorem stokesFlow_smallPastDissipationRatio_packet
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
                    0 < normalizedKineticEnergy S.velocity t ∧
                      0 <
                        coordinateEnergyDissipationRate S.velocity ν t /
                          normalizedKineticEnergy S.velocity t ∧
                        coordinateEnergyDissipationRate S.velocity ν t /
                            normalizedKineticEnergy S.velocity t < lam := by
  exact
    ⟨S.nonzeroStokesFlowKernel hconv hpressure,
      S.exists_nonzero_endpoint_with_arbitrarily_small_past_dissipation_ratio hν⟩

/-- Exact Stokes-flow specialization of the spatial Rayleigh-quotient
collapse: a positive-viscosity nonzero Stokes candidate has arbitrarily small
positive past coordinate-enstrophy quotients. -/
theorem stokesFlow_smallPastCoordinateEnstrophyRatio_packet
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
                  0 < coordinateEnstrophyAt S.velocity t ∧
                    0 < normalizedKineticEnergy S.velocity t ∧
                      0 <
                        coordinateEnstrophyAt S.velocity t /
                          normalizedKineticEnergy S.velocity t ∧
                        coordinateEnstrophyAt S.velocity t /
                            normalizedKineticEnergy S.velocity t < lam := by
  rcases S.nonzero_velocity with ⟨T, xT, hneT⟩
  refine ⟨S.nonzeroStokesFlowKernel hconv hpressure, T, xT, hneT, ?_⟩
  intro lam hlam
  exact
    S.toSchwartzConcreteNavierStokesSolution
      |>.exists_past_nonzero_with_small_positive_coordinateEnstrophy_ratio
        hν ⟨xT, hneT⟩ hlam

/-- Exact Stokes-flow specialization of the spatial Poincare-floor
obstruction: no positive-viscosity nonzero Stokes candidate can keep a
positive coordinate-enstrophy floor over normalized energy on the whole past
ray of a nonzero endpoint. -/
theorem stokesFlow_noPastCoordinateEnstrophyFloor_packet
    (hν : 0 < ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {lam T : NSTime} (hlam : 0 < lam)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      ¬ ∀ t : NSTime, t ≤ T →
        lam * normalizedKineticEnergy S.velocity t ≤
          coordinateEnstrophyAt S.velocity t := by
  exact
    ⟨S.nonzeroStokesFlowKernel hconv hpressure,
      S.toSchwartzConcreteNavierStokesSolution
        |>.not_forall_past_coordinateEnstrophyAt_ge_mul_normalizedKineticEnergy
          hν hlam hneT⟩

/-- Exact Stokes-flow specialization of the spatial Rayleigh-quotient floor
obstruction: no positive-viscosity nonzero Stokes candidate can keep a positive
lower bound on coordinate enstrophy divided by normalized kinetic energy along
the whole past ray of a nonzero endpoint. -/
theorem stokesFlow_noPastCoordinateEnstrophyRatioFloor_packet
    (hν : 0 < ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {lam T : NSTime} (hlam : 0 < lam)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      ¬ ∀ t : NSTime, t ≤ T →
        lam ≤
          coordinateEnstrophyAt S.velocity t /
            normalizedKineticEnergy S.velocity t := by
  refine ⟨S.nonzeroStokesFlowKernel hconv hpressure, ?_⟩
  intro hfloor
  rcases S.toSchwartzConcreteNavierStokesSolution
      |>.exists_past_nonzero_with_small_positive_coordinateEnstrophy_ratio
        hν hneT hlam with
    ⟨t, htT, _hne, _hEnstpos, _hEpos, _hratio_pos, hratio_lt⟩
  exact not_le_of_gt hratio_lt (hfloor t htT)

/-- General exact spatial Rayleigh-equality obstruction: no
positive-viscosity nonzero candidate can keep
`coordinateEnstrophyAt = lam * normalizedKineticEnergy` on the whole past ray
of a nonzero endpoint. -/
theorem noPastExactCoordinateEnstrophyRayleigh_packet
    (hν : 0 < ν) {lam T : NSTime} (hlam : 0 < lam)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    ¬ ∀ t : NSTime, t ≤ T →
      coordinateEnstrophyAt S.velocity t =
        lam * normalizedKineticEnergy S.velocity t := by
  intro heq
  exact
    (S.toSchwartzConcreteNavierStokesSolution
      |>.not_forall_past_coordinateEnstrophyAt_ge_mul_normalizedKineticEnergy
        hν hlam hneT)
      (by
        intro t ht
        exact le_of_eq ((heq t ht).symm))

/-- General exact spatial Rayleigh-quotient obstruction: no
positive-viscosity nonzero candidate can keep
`coordinateEnstrophyAt / normalizedKineticEnergy = lam` on the whole past ray
of a nonzero endpoint. -/
theorem noPastExactCoordinateEnstrophyRatioRayleigh_packet
    (hν : 0 < ν) {lam T : NSTime} (hlam : 0 < lam)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    ¬ ∀ t : NSTime, t ≤ T →
      coordinateEnstrophyAt S.velocity t /
        normalizedKineticEnergy S.velocity t = lam := by
  intro heq
  rcases S.toSchwartzConcreteNavierStokesSolution
      |>.exists_past_nonzero_with_small_positive_coordinateEnstrophy_ratio
        hν hneT hlam with
    ⟨t, htT, _hne, _hEnstpos, _hEpos, _hratio_pos, hratio_lt⟩
  exact not_le_of_gt hratio_lt (le_of_eq ((heq t htT).symm))

/-- Exact Stokes-flow obstruction to fixed positive spatial Rayleigh equality:
no positive-viscosity nonzero Stokes candidate can keep
`coordinateEnstrophyAt = lam * normalizedKineticEnergy` on the whole past ray
of a nonzero endpoint. -/
theorem stokesFlow_noPastExactCoordinateEnstrophyRayleigh_packet
    (hν : 0 < ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {lam T : NSTime} (hlam : 0 < lam)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      ¬ ∀ t : NSTime, t ≤ T →
        coordinateEnstrophyAt S.velocity t =
          lam * normalizedKineticEnergy S.velocity t := by
  refine ⟨S.nonzeroStokesFlowKernel hconv hpressure, ?_⟩
  intro heq
  exact
    (S.stokesFlow_noPastCoordinateEnstrophyFloor_packet
      hν hconv hpressure hlam hneT).2
      (by
        intro t ht
        exact le_of_eq ((heq t ht).symm))

/-- Exact Stokes-flow obstruction to fixed positive spatial Rayleigh-quotient
equality: no positive-viscosity nonzero Stokes candidate can keep
`coordinateEnstrophyAt / normalizedKineticEnergy = lam` on the whole past ray
of a nonzero endpoint. -/
theorem stokesFlow_noPastExactCoordinateEnstrophyRatioRayleigh_packet
    (hν : 0 < ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {lam T : NSTime} (hlam : 0 < lam)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      ¬ ∀ t : NSTime, t ≤ T →
        coordinateEnstrophyAt S.velocity t /
          normalizedKineticEnergy S.velocity t = lam := by
  refine ⟨S.nonzeroStokesFlowKernel hconv hpressure, ?_⟩
  intro heq
  exact
    (S.stokesFlow_noPastCoordinateEnstrophyRatioFloor_packet
      hν hconv hpressure hlam hneT).2
      (by
        intro t ht
        exact le_of_eq ((heq t ht).symm))

/-- Positive-viscosity Stokes profile-gap obstruction packet: any nonzero
Stokes candidate carries the Stokes kernel, but whole-past spectral,
coordinate-enstrophy, and spatial Rayleigh-quotient floors all fail before a
nonzero endpoint, with an explicit small positive spatial Rayleigh sample. -/
theorem stokesFlow_positiveViscosity_profileGapObstruction_packet
    (hν : 0 < ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {lam T : NSTime} (hlam : 0 < lam)
    (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      (¬ ∀ t : NSTime, t ≤ T →
        lam * normalizedKineticEnergy S.velocity t ≤
          coordinateEnergyDissipationRate S.velocity ν t) ∧
      (¬ ∀ t : NSTime, t ≤ T →
        lam * normalizedKineticEnergy S.velocity t ≤
          coordinateEnstrophyAt S.velocity t) ∧
      (¬ ∀ t : NSTime, t ≤ T →
        lam ≤
          coordinateEnstrophyAt S.velocity t /
            normalizedKineticEnergy S.velocity t) ∧
      ∃ t : NSTime,
        t ≤ T ∧
          (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
            0 < coordinateEnstrophyAt S.velocity t ∧
              0 < normalizedKineticEnergy S.velocity t ∧
                0 <
                  coordinateEnstrophyAt S.velocity t /
                    normalizedKineticEnergy S.velocity t ∧
                  coordinateEnstrophyAt S.velocity t /
                      normalizedKineticEnergy S.velocity t < lam := by
  refine
    ⟨S.nonzeroStokesFlowKernel hconv hpressure,
      S.toSchwartzConcreteNavierStokesSolution
        |>.not_forall_past_coordinateEnergyDissipationRate_ge_mul_normalizedKineticEnergy
          hν.le hlam hneT,
      (S.stokesFlow_noPastCoordinateEnstrophyFloor_packet
        hν hconv hpressure hlam hneT).2,
      (S.stokesFlow_noPastCoordinateEnstrophyRatioFloor_packet
        hν hconv hpressure hlam hneT).2,
      S.toSchwartzConcreteNavierStokesSolution
        |>.exists_past_nonzero_with_small_positive_coordinateEnstrophy_ratio
          hν hneT hlam⟩

/-- Endpoint-parametric Stokes obstruction packet: before any chosen nonzero
endpoint, a positive-viscosity exact Stokes candidate has strict past energy
ordering and arbitrarily small positive spatial Rayleigh samples. -/
theorem stokesFlow_endpointStrictEnergy_and_smallPastCoordinateEnstrophyRatio_packet
    (hν : 0 < ν)
    (hconv : ∀ t x, spatialConvection S.velocity t x = 0)
    (hpressure : ∀ t x, spatialPressureGradient S.pressure t x = 0)
    {T : NSTime} (hneT : ∃ xT : NSSpace, S.velocity T xT ≠ 0) :
    NonzeroSchwartzStokesFlowKernel ν S.velocity S.pressure ∧
      SchwartzNonzeroTimeSupportKernel ν S.velocity S.pressure ∧
      (∀ {s t : NSTime}, s < t → t ≤ T →
        normalizedKineticEnergy S.velocity t <
          normalizedKineticEnergy S.velocity s) ∧
      ∀ lam : NSTime, 0 < lam →
        ∃ t : NSTime,
          t ≤ T ∧
            (∃ x : NSSpace, S.velocity t x ≠ 0) ∧
              0 < coordinateEnstrophyAt S.velocity t ∧
                0 < normalizedKineticEnergy S.velocity t ∧
                  0 <
                    coordinateEnstrophyAt S.velocity t /
                      normalizedKineticEnergy S.velocity t ∧
                    coordinateEnstrophyAt S.velocity t /
                        normalizedKineticEnergy S.velocity t < lam := by
  exact
    ⟨S.nonzeroStokesFlowKernel hconv hpressure,
      S.nonzeroTimeSupportKernel,
      fun {_s _t} hst htT =>
        S.normalizedKineticEnergy_strict_lt_before_nonzero_endpoint_of_pos_viscosity
          hν hst htT hneT,
      fun lam hlam =>
        S.toSchwartzConcreteNavierStokesSolution
          |>.exists_past_nonzero_with_small_positive_coordinateEnstrophy_ratio
            hν hneT hlam⟩

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

/-- Global no-go form for uniform future dissipation gaps in the nonzero
slice-Schwartz interface. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_uniform_future_dissipation_gap
    {ν κ : ℝ} (hκ : 0 < κ) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ T : NSTime,
        ∀ t : NSTime, T ≤ t →
          κ ≤ coordinateEnergyDissipationRate S.velocity ν t := by
  rintro ⟨S, T, hgap⟩
  exact
    (S.toSchwartzConcreteNavierStokesSolution
      |>.not_forall_future_coordinateEnergyDissipationRate_ge hκ) hgap

/-- Global Stokes-flow no-go form for uniform future dissipation gaps. -/
theorem not_exists_nonzeroSchwartzStokesFlow_uniform_future_dissipation_gap
    {ν κ : ℝ} (hκ : 0 < κ) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      (∀ t x, spatialConvection S.velocity t x = 0) ∧
        (∀ t x, spatialPressureGradient S.pressure t x = 0) ∧
          ∃ T : NSTime,
            ∀ t : NSTime, T ≤ t →
              κ ≤ coordinateEnergyDissipationRate S.velocity ν t := by
  rintro ⟨S, _hconv, _hpressure, T, hgap⟩
  exact
    (S.toSchwartzConcreteNavierStokesSolution
      |>.not_forall_future_coordinateEnergyDissipationRate_ge hκ) hgap

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

/-- Global no-go form for positive lower bounds on the whole-past corrected
dissipation Rayleigh quotient in the nonzero slice-Schwartz interface. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_past_dissipation_ratio_floor
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ T : NSTime,
        (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
          ∀ t : NSTime, t ≤ T →
            lam ≤
              coordinateEnergyDissipationRate S.velocity ν t /
                normalizedKineticEnergy S.velocity t := by
  rintro ⟨S, T, hneT, hfloor⟩
  rcases S.toSchwartzConcreteNavierStokesSolution
      |>.exists_past_nonzero_with_small_positive_dissipation_ratio
        hν hneT hlam with
    ⟨t, htT, _hne, _hDpos, _hEpos, _hratio_pos, hratio_lt⟩
  exact not_le_of_gt hratio_lt (hfloor t htT)

/-- Global no-go form for positive lower bounds on the whole-past spatial
coordinate-enstrophy Rayleigh quotient in the nonzero slice-Schwartz
interface. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_past_coordinateEnstrophy_ratio_floor
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ T : NSTime,
        (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
          ∀ t : NSTime, t ≤ T →
            lam ≤
              coordinateEnstrophyAt S.velocity t /
                normalizedKineticEnergy S.velocity t := by
  rintro ⟨S, T, hneT, hfloor⟩
  rcases S.toSchwartzConcreteNavierStokesSolution
      |>.exists_past_nonzero_with_small_positive_coordinateEnstrophy_ratio
        hν hneT hlam with
    ⟨t, htT, _hne, _hEnstpos, _hEpos, _hratio_pos, hratio_lt⟩
  exact not_le_of_gt hratio_lt (hfloor t htT)

/-- Global no-go form for positive spatial Poincare floors on a whole past ray
before a nonzero endpoint. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_past_coordinateEnstrophy_floor
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ T : NSTime,
        (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
          ∀ t : NSTime, t ≤ T →
            lam * normalizedKineticEnergy S.velocity t ≤
              coordinateEnstrophyAt S.velocity t := by
  rintro ⟨S, T, hneT, hfloor⟩
  exact
    (S.toSchwartzConcreteNavierStokesSolution
      |>.not_forall_past_coordinateEnstrophyAt_ge_mul_normalizedKineticEnergy
        hν hlam hneT) hfloor

/-- Global no-go form for exact positive coordinate-enstrophy Rayleigh
equality on a whole past ray before a nonzero endpoint. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_past_exact_coordinateEnstrophyRayleigh_of_posViscosity
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ T : NSTime,
        (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
          ∀ t : NSTime, t ≤ T →
            coordinateEnstrophyAt S.velocity t =
              lam * normalizedKineticEnergy S.velocity t := by
  rintro ⟨S, T, hneT, heq⟩
  exact S.noPastExactCoordinateEnstrophyRayleigh_packet hν hlam hneT heq

/-- Global no-go form for exact positive spatial Rayleigh-quotient equality on
a whole past ray before a nonzero endpoint. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_past_exact_coordinateEnstrophyRatioRayleigh_of_posViscosity
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ T : NSTime,
        (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
          ∀ t : NSTime, t ≤ T →
            coordinateEnstrophyAt S.velocity t /
              normalizedKineticEnergy S.velocity t = lam := by
  rintro ⟨S, T, hneT, heq⟩
  exact S.noPastExactCoordinateEnstrophyRatioRayleigh_packet hν hlam hneT heq

/-- Global Stokes-flow no-go form for positive spatial Poincare floors on a
whole past ray before a nonzero endpoint. -/
theorem not_exists_nonzeroSchwartzStokesFlow_past_coordinateEnstrophy_floor_of_posViscosity
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      (∀ t x, spatialConvection S.velocity t x = 0) ∧
        (∀ t x, spatialPressureGradient S.pressure t x = 0) ∧
          ∃ T : NSTime,
            (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
              ∀ t : NSTime, t ≤ T →
                lam * normalizedKineticEnergy S.velocity t ≤
                  coordinateEnstrophyAt S.velocity t := by
  rintro ⟨S, hconv, hpressure, T, hneT, hfloor⟩
  exact
    (S.stokesFlow_noPastCoordinateEnstrophyFloor_packet
      hν hconv hpressure hlam hneT).2 hfloor

/-- Global Stokes-flow no-go form for positive whole-past spatial
Rayleigh-quotient floors before a nonzero endpoint. -/
theorem not_exists_nonzeroSchwartzStokesFlow_past_coordinateEnstrophy_ratio_floor_of_posViscosity
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      (∀ t x, spatialConvection S.velocity t x = 0) ∧
        (∀ t x, spatialPressureGradient S.pressure t x = 0) ∧
          ∃ T : NSTime,
            (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
              ∀ t : NSTime, t ≤ T →
                lam ≤
                  coordinateEnstrophyAt S.velocity t /
                    normalizedKineticEnergy S.velocity t := by
  rintro ⟨S, hconv, hpressure, T, hneT, hfloor⟩
  exact
    (S.stokesFlow_noPastCoordinateEnstrophyRatioFloor_packet
      hν hconv hpressure hlam hneT).2 hfloor

/-- Global Stokes-flow no-go form for exact positive coordinate-enstrophy
Rayleigh equality on a whole past ray before a nonzero endpoint. -/
theorem not_exists_nonzeroSchwartzStokesFlow_past_exact_coordinateEnstrophyRayleigh_of_posViscosity
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      (∀ t x, spatialConvection S.velocity t x = 0) ∧
        (∀ t x, spatialPressureGradient S.pressure t x = 0) ∧
          ∃ T : NSTime,
            (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
              ∀ t : NSTime, t ≤ T →
                coordinateEnstrophyAt S.velocity t =
                  lam * normalizedKineticEnergy S.velocity t := by
  rintro ⟨S, hconv, hpressure, T, hneT, heq⟩
  exact
    (S.stokesFlow_noPastExactCoordinateEnstrophyRayleigh_packet
      hν hconv hpressure hlam hneT).2 heq

/-- Global Stokes-flow no-go form for exact positive spatial Rayleigh-quotient
equality on a whole past ray before a nonzero endpoint. -/
theorem not_exists_nonzeroSchwartzStokesFlow_past_exact_coordinateEnstrophyRatioRayleigh_of_posViscosity
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      (∀ t x, spatialConvection S.velocity t x = 0) ∧
        (∀ t x, spatialPressureGradient S.pressure t x = 0) ∧
          ∃ T : NSTime,
            (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
              ∀ t : NSTime, t ≤ T →
                coordinateEnstrophyAt S.velocity t /
                  normalizedKineticEnergy S.velocity t = lam := by
  rintro ⟨S, hconv, hpressure, T, hneT, heq⟩
  exact
    (S.stokesFlow_noPastExactCoordinateEnstrophyRatioRayleigh_packet
      hν hconv hpressure hlam hneT).2 heq

/-- One-profile route-facing no-go: a positive-viscosity nonzero
slice-Schwartz solution represented as a fixed Schwartz profile times a scalar
amplitude cannot keep exact positive spatial Rayleigh equality on the whole
past ray of a nonzero endpoint. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_oneProfile_past_exact_coordinateEnstrophyRayleigh_of_posViscosity
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity) (T : NSTime),
        S.velocity = (fun r y => a r • f y) ∧
          (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
            ∀ t : NSTime, t ≤ T →
              coordinateEnstrophyAt (fun r y => a r • f y) t =
                lam * normalizedKineticEnergy (fun r y => a r • f y) t := by
  rintro ⟨S, a, f, T, hvelocity, hneT, heq⟩
  exact
    not_exists_nonzeroSchwartzConcreteSolution_past_exact_coordinateEnstrophyRayleigh_of_posViscosity
      hν hlam
      ⟨S, T, hneT, by
        intro t ht
        simpa [hvelocity] using heq t ht⟩

/-- One-profile route-facing no-go: a positive-viscosity nonzero
slice-Schwartz solution represented as a fixed Schwartz profile times a scalar
amplitude cannot keep exact positive spatial Rayleigh-quotient equality on the
whole past ray of a nonzero endpoint. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_oneProfile_past_exact_coordinateEnstrophyRatioRayleigh_of_posViscosity
    {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 < lam) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity) (T : NSTime),
        S.velocity = (fun r y => a r • f y) ∧
          (∃ xT : NSSpace, S.velocity T xT ≠ 0) ∧
            ∀ t : NSTime, t ≤ T →
              coordinateEnstrophyAt (fun r y => a r • f y) t /
                  normalizedKineticEnergy (fun r y => a r • f y) t =
                lam := by
  rintro ⟨S, a, f, T, hvelocity, hneT, heq⟩
  exact
    not_exists_nonzeroSchwartzConcreteSolution_past_exact_coordinateEnstrophyRatioRayleigh_of_posViscosity
      hν hlam
      ⟨S, T, hneT, by
        intro t ht
        simpa [hvelocity] using heq t ht⟩

/-- Fundamental fixed-profile obstruction: no positive-viscosity nonzero
slice-Schwartz concrete solution can be represented by a single scalar amplitude
times one fixed Schwartz profile.  A nonzero endpoint makes the profile's
spatial Rayleigh quotient a fixed positive constant on the whole past ray, which
contradicts the bounded-eternal Rayleigh-collapse theorem. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_oneProfile_of_posViscosity
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity),
        S.velocity = fun r y => a r • f y := by
  rintro ⟨S, a, f, hvelocity⟩
  rcases S.nonzero_velocity with ⟨T, xT, hneT⟩
  let u : NSVelocityField := fun r y => a r • f y
  let M : ℝ := ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume
  let G : ℝ := coordinateEnstrophyAt
    (timeIndependentVelocity (f : NSInitialVelocity)) 0
  have hfne : ∃ x : NSSpace, f x ≠ 0 := by
    refine ⟨xT, ?_⟩
    intro hfx
    have hzero : S.velocity T xT = 0 := by
      rw [hvelocity]
      simp [hfx]
    exact hneT hzero
  have hMpos : 0 < M := by
    dsimp [M]
    exact integral_norm_sq_pos_of_schwartz_ne_zero f hfne
  have hcoordFormula :
      ∀ t : NSTime, coordinateEnstrophyAt u t = (a t) ^ (2 : ℕ) * G := by
    intro t
    dsimp [u, G]
    exact congrFun (coordinateEnstrophyAt_scalar_smul_schwartz a f) t
  have henergyFormula :
      ∀ t : NSTime,
        normalizedKineticEnergy u t =
          (1 / 2 : ℝ) * ((a t) ^ (2 : ℕ) * M) := by
    intro t
    dsimp [u, M]
    exact congrFun (normalizedKineticEnergy_scalar_smul_schwartz a f) t
  have haT_ne : a T ≠ 0 := by
    intro haT
    have hzero : S.velocity T xT = 0 := by
      rw [hvelocity]
      simp [haT]
    exact hneT hzero
  have hcoordTpos : 0 < coordinateEnstrophyAt u T := by
    have hpos :
        0 < coordinateEnstrophyAt S.velocity T :=
      S.toSchwartzConcreteNavierStokesSolution
        |>.coordinateEnstrophyAt_pos_of_velocity_ne_zero hneT
    simpa [u, hvelocity] using hpos
  have hGpos : 0 < G := by
    have hcoordT := hcoordFormula T
    rw [hcoordT] at hcoordTpos
    have haTpos : 0 < (a T) ^ (2 : ℕ) := sq_pos_of_ne_zero haT_ne
    nlinarith
  let lam : ℝ := (2 * G) / M
  have hlam : 0 < lam := by
    dsimp [lam]
    exact div_pos (mul_pos (by norm_num) hGpos) hMpos
  have heq : ∀ t : NSTime, t ≤ T →
      coordinateEnstrophyAt S.velocity t =
        lam * normalizedKineticEnergy S.velocity t := by
    intro t _ht
    have hcoord := hcoordFormula t
    have henergy := henergyFormula t
    calc
      coordinateEnstrophyAt S.velocity t = coordinateEnstrophyAt u t := by
        rw [hvelocity]
      _ = (a t) ^ (2 : ℕ) * G := hcoord
      _ = lam * ((1 / 2 : ℝ) * ((a t) ^ (2 : ℕ) * M)) := by
        dsimp [lam]
        field_simp [ne_of_gt hMpos]
      _ = lam * normalizedKineticEnergy u t := by
        rw [henergy]
      _ = lam * normalizedKineticEnergy S.velocity t := by
        rw [hvelocity]
  exact
    (not_exists_nonzeroSchwartzConcreteSolution_past_exact_coordinateEnstrophyRayleigh_of_posViscosity
      hν hlam)
      ⟨S, T, ⟨xT, hneT⟩, heq⟩

/-- Exact Stokes-flow specialization of the fixed-profile obstruction: a
positive-viscosity nonzero zero-convection, zero-pressure-gradient candidate
cannot stay in a single scalar-modulated Schwartz profile. -/
theorem not_exists_nonzeroSchwartzStokesFlow_oneProfile_of_posViscosity
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      (∀ t x, spatialConvection S.velocity t x = 0) ∧
        (∀ t x, spatialPressureGradient S.pressure t x = 0) ∧
          ∃ (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity),
            S.velocity = fun r y => a r • f y := by
  rintro ⟨S, _hconv, _hpressure, a, f, hvelocity⟩
  exact
    not_exists_nonzeroSchwartzConcreteSolution_oneProfile_of_posViscosity hν
      ⟨S, a, f, hvelocity⟩

end NavierStokes
end FluidDynamics
end Mettapedia
