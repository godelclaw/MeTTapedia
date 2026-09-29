import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoreEnvelope

/-!
# A pressure heat defect at zero receiver gradients

The companion lab constructs the solenoidal periodic two-wave datum
`(sin(n(x+y)), 2sin(nx)-sin(n(x+y)), sin(nx)-sin(n(x+y)))`.
Its mean squared speed is four for every positive integer `n`. At the
origin, all first spatial derivatives of strain, vorticity and pressure
Hessian vanish, but the complete scalar parabolic viscosity contribution
to the current reserve is positive. Its normalized size grows as `ν n²`.

The Fourier realization, actual NS tangent and viscous source identity
are analytic and exact-symbolically checked in `viscous_parent_memory.py`.
This file certifies the scalar family, its bounds and its unbounded
normalized rate. A positive parabolic defect does not assert temporal
heat growth, singularity, or failure of a full-datum history allowance.
Retaining the viscous quadratic-variation tensor cancels the identified
pressure source; its nearby pressure action still needs a history bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureViscousMemory

open PressureCoreEnvelope

def familyReserve (r : ℝ) : ℝ :=
  reserve 1 1 ((9/2) * r ^ 2) (r ^ 2) (r ^ 3) (2 * r ^ 4) (-(8/5) * r ^ 4)

def familyWeight (r : ℝ) : ℝ := weight 1 ((4/35) * r ^ 4)

def heatDefect (ν r : ℝ) : ℝ := (32/5) * ν * familyWeight r * r ^ 6

theorem family_gap (r : ℝ) :
    pressure 1 (r ^ 2) (r ^ 3) (-(8/5) * r ^ 4) -
      core 1 ((9/2) * r ^ 2) (r ^ 2) (r ^ 3) (2 * r ^ 4) = (4/35) * r ^ 4 := by
  dsimp [pressure, core]
  ring

theorem family_weight_ge_half (r : ℝ) : (1/2 : ℝ) ≤ familyWeight r := by
  have h : 0 ≤ ((4/35) * r ^ 4) / Real.sqrt (((4/35) * r ^ 4) ^ 2 + 1 ^ 2) := by
    positivity
  dsimp [familyWeight, weight]
  linarith

private theorem family_reserve_pos (r : ℝ) : 0 < familyReserve r := by
  have h := reserve_coercive 1 1 ((9/2) * r ^ 2) (r ^ 2) (r ^ 3) (2 * r ^ 4)
    (-(8/5) * r ^ 4) (by norm_num) (by positivity) (by positivity) (by positivity)
  change 0 < reserve 1 1 ((9/2) * r ^ 2) (r ^ 2) (r ^ 3) (2 * r ^ 4) (-(8/5) * r ^ 4)
  nlinarith [sq_nonneg (r ^ 2)]

theorem family_reserve_upper (r : ℝ) (hr : 1 ≤ r) : familyReserve r ≤ 11 * r ^ 4 := by
  have hd : 0 < r ^ 2 + 1 := by positivity
  have ht : 5 * (r ^ 3) ^ 2 / (r ^ 2 + 1) ≤ 5 * r ^ 4 := by
    apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg (r ^ 2)]
  have hp : pressure 1 (r ^ 2) (r ^ 3) (-(8/5) * r ^ 4) ≤ (842/95) * r ^ 4 := by
    dsimp [pressure]
    nlinarith only [ht]
  have hg := family_gap r
  have hc : core 1 ((9/2) * r ^ 2) (r ^ 2) (r ^ 3) (2 * r ^ 4) ≤ (842/95) * r ^ 4 := by
    nlinarith [sq_nonneg (r ^ 2)]
  have h := reserve_le_of_branches_le 1 1 ((9/2) * r ^ 2) (r ^ 2) (r ^ 3)
    (2 * r ^ 4) (-(8/5) * r ^ 4) ((842/95) * r ^ 4) (by norm_num) hp hc
  have hr4 : 1 ≤ r ^ 4 := one_le_pow₀ hr
  change reserve 1 1 ((9/2) * r ^ 2) (r ^ 2) (r ^ 3) (2 * r ^ 4) (-(8/5) * r ^ 4) ≤ _
  linarith

theorem heat_defect_lower (ν r : ℝ) (hν : 0 ≤ ν) :
    (16/5) * ν * r ^ 6 ≤ heatDefect ν r := by
  have h := mul_le_mul_of_nonneg_right (family_weight_ge_half r)
    (show 0 ≤ (32/5) * ν * r ^ 6 by positivity)
  dsimp [heatDefect]
  nlinarith only [h]

theorem normalized_heat_lower (ν r : ℝ) (hν : 0 ≤ ν) (hr : 1 ≤ r) :
    (16/55) * ν * r ^ 2 ≤ heatDefect ν r / familyReserve r := by
  apply (le_div_iff₀ (family_reserve_pos r)).2
  have hu := mul_le_mul_of_nonneg_left (family_reserve_upper r hr)
    (show 0 ≤ (16/55) * ν * r ^ 2 by positivity)
  have hl := heat_defect_lower ν r hν
  nlinarith only [hu, hl]

/-- No fixed energy-only instantaneous coefficient can dominate this
normalized scalar heat defect. This is not a time-integral assertion. -/
theorem normalized_heat_unbounded (ν B : ℝ) (hν : 0 < ν) :
    ∃ n : ℕ, 1 ≤ n ∧ B < heatDefect ν n / familyReserve n := by
  let a : ℝ := (16/55) * ν
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (B / a))
  have hn1 : 1 ≤ (n : ℝ) := (le_max_left _ _).trans hn.le
  have hnB : B / a < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hB : B < a * (n : ℝ) := by
    have h := (div_lt_iff₀ ha).1 hnB
    nlinarith only [h]
  refine ⟨n, ?_, ?_⟩
  · exact_mod_cast hn1
  · calc
      B < a * (n : ℝ) := hB
      _ ≤ a * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) ha.le
      _ ≤ _ := normalized_heat_lower ν n hν.le hn1

end Mettapedia.FluidDynamics.NavierStokes.PressureViscousMemory
