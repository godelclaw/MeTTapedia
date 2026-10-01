import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# A heat-gradient observation does not automatically obey fluid evolution

A positive scalar heat profile has zero initial gradient at the observed
point, followed by a nonzero gradient. Identity-gradient reconstruction
through a tight solenoidal frame therefore needs an evolution compatibility
condition in addition to initial matching. The companion analytic argument
treats both composition conventions and gives the full forced shear.

This module certifies the scalar heat profile, its log-gradient observation,
the nonzero fluid residual and a delayed example whose initial residual is
zero. Group heat identification, the spatial frame and the general
arbitrarily delayed family remain analytic in the companion lab. These
observations are not unforced NS evolutions from zero data.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.HeatGradientObserver

def heat (ν k t : ℝ) : ℝ := Real.exp (-(k * ν) * t)

theorem heat_derivative (ν k t : ℝ) :
    HasDerivAt (heat ν k) (-(k * ν) * heat ν k t) t := by
  apply (((hasDerivAt_id t).const_mul (-(k * ν))).exp).congr_deriv
  dsimp [heat]
  ring

@[simp] theorem heat_zero (ν k : ℝ) : heat ν k 0 = 1 := by simp [heat]

def profile (ν t x : ℝ) : ℝ :=
  2 + heat ν 1 t * Real.sin x - heat ν 4 t * Real.sin (2 * x) / 2

def profileX (ν t x : ℝ) : ℝ :=
  heat ν 1 t * Real.cos x - heat ν 4 t * Real.cos (2 * x)

def profileXX (ν t x : ℝ) : ℝ :=
  -heat ν 1 t * Real.sin x + 2 * heat ν 4 t * Real.sin (2 * x)

theorem profile_lower (ν t x : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    (1 / 2 : ℝ) ≤ profile ν t x := by
  have h1 : 0 < heat ν 1 t := Real.exp_pos _
  have h4 : 0 < heat ν 4 t := Real.exp_pos _
  have h1b : heat ν 1 t ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h4b : heat ν 4 t ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hl := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin x) h1.le
  have hu := mul_le_mul_of_nonneg_left (Real.sin_le_one (2 * x)) h4.le
  dsimp [profile]
  nlinarith

theorem profile_space (ν t x : ℝ) :
    HasDerivAt (profile ν t) (profileX ν t x) x := by
  have h := ((Real.hasDerivAt_sin x).const_mul (heat ν 1 t)).const_add 2 |>.sub
    (((((hasDerivAt_id x).const_mul 2).sin).const_mul (heat ν 4 t)).div_const 2)
  apply h.congr_deriv
  dsimp [profileX]
  ring

theorem profile_space_second (ν t x : ℝ) :
    HasDerivAt (profileX ν t) (profileXX ν t x) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul (heat ν 1 t)).sub
    ((((hasDerivAt_id x).const_mul 2).cos).const_mul (heat ν 4 t))
  apply h.congr_deriv
  dsimp [profileXX]
  ring

theorem profile_heat (ν t x : ℝ) :
    HasDerivAt (fun s ↦ profile ν s x) (ν * profileXX ν t x) t := by
  have h := (((heat_derivative ν 1 t).mul_const (Real.sin x)).const_add 2).sub
    (((heat_derivative ν 4 t).mul_const (Real.sin (2 * x))).div_const 2)
  apply h.congr_deriv
  dsimp [profileXX]
  ring

@[simp] theorem profile_origin (ν t : ℝ) : profile ν t 0 = 2 := by simp [profile]

@[simp] theorem initial_profile_gradient (ν : ℝ) : profileX ν 0 0 = 0 := by
  simp [profileX]

def potential (ν t x : ℝ) : ℝ := -2 * ν * Real.log (profile ν t x)

theorem potential_space_origin (ν t : ℝ) :
    HasDerivAt (potential ν t) (-ν * (heat ν 1 t - heat ν 4 t)) 0 := by
  have h := ((profile_space ν t 0).log (by simp)).const_mul (-2 * ν)
  apply h.congr_deriv
  simp only [profile_origin, profileX, Real.cos_zero, mul_zero, mul_one]
  ring

/-- `κ=0` and `κ=1` are the two finite-frame composition conventions. -/
def amplitude (ν κ t : ℝ) : ℝ :=
  ν * (heat ν (κ + 1) t - heat ν (κ + 4) t)

def amplitudeRate (ν κ t : ℝ) : ℝ :=
  ν ^ 2 * (-(κ + 1) * heat ν (κ + 1) t + (κ + 4) * heat ν (κ + 4) t)

def fluidSource (ν κ t : ℝ) : ℝ :=
  ν ^ 2 * (-κ * heat ν (κ + 1) t + (κ + 3) * heat ν (κ + 4) t)

theorem amplitude_derivative (ν κ t : ℝ) :
    HasDerivAt (amplitude ν κ) (amplitudeRate ν κ t) t := by
  apply (((heat_derivative ν (κ + 1) t).sub (heat_derivative ν (κ + 4) t)).const_mul ν).congr_deriv
  unfold amplitudeRate
  ring

@[simp] theorem amplitude_zero (ν κ : ℝ) : amplitude ν κ 0 = 0 := by simp [amplitude]

theorem amplitude_pos (ν κ t : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    0 < amplitude ν κ t := by
  apply mul_pos hν
  apply sub_pos.mpr
  apply Real.exp_lt_exp.mpr
  nlinarith [mul_pos hν ht]

theorem observation_from_log_gradient (ν t : ℝ) :
    -deriv (potential ν t) 0 = amplitude ν 0 t := by
  rw [(potential_space_origin ν t).deriv]
  simp only [amplitude, zero_add]
  ring

theorem full_fluid_source (ν κ t : ℝ) :
    amplitudeRate ν κ t + ν * amplitude ν κ t = fluidSource ν κ t := by
  unfold amplitudeRate amplitude fluidSource
  ring

@[simp] theorem initial_source (ν κ : ℝ) : fluidSource ν κ 0 = 3 * ν ^ 2 := by
  simp only [fluidSource, heat_zero, mul_one]
  ring

theorem not_unforced_initial_rate (ν κ : ℝ) (hν : 0 < ν) :
    ¬ HasDerivAt (amplitude ν κ) (-ν * amplitude ν κ 0) 0 := by
  intro h
  have he := (amplitude_derivative ν κ 0).unique h
  simp only [amplitudeRate, heat_zero, mul_one, amplitude_zero, mul_zero] at he
  nlinarith [sq_pos_of_pos hν]

/-- The initial heat perturbation is `sin(x)^5` in this delayed case. -/
def delayed (ν κ t : ℝ) : ℝ :=
  ν / 16 * (10 * heat ν (κ + 1) t - 15 * heat ν (κ + 9) t + 5 * heat ν (κ + 25) t)

def delayedRate (ν κ t : ℝ) : ℝ :=
  ν ^ 2 / 16 * (-10 * (κ + 1) * heat ν (κ + 1) t +
    15 * (κ + 9) * heat ν (κ + 9) t - 5 * (κ + 25) * heat ν (κ + 25) t)

theorem delayed_derivative (ν κ t : ℝ) :
    HasDerivAt (delayed ν κ) (delayedRate ν κ t) t := by
  have h := (((((heat_derivative ν (κ + 1) t).const_mul 10).sub
    ((heat_derivative ν (κ + 9) t).const_mul 15)).add
      ((heat_derivative ν (κ + 25) t).const_mul 5)).const_mul (ν / 16))
  apply h.congr_deriv
  unfold delayedRate
  ring

@[simp] theorem delayed_zero (ν κ : ℝ) : delayed ν κ 0 = 0 := by
  norm_num [delayed]

@[simp] theorem delayedRate_zero (ν κ : ℝ) : delayedRate ν κ 0 = 0 := by
  simp only [delayedRate, heat_zero, mul_one]
  ring

theorem delayed_acceleration (ν κ : ℝ) :
    HasDerivAt (delayedRate ν κ) (120 * ν ^ 3) 0 := by
  have h := (((((heat_derivative ν (κ + 1) 0).const_mul (-10 * (κ + 1))).add
    ((heat_derivative ν (κ + 9) 0).const_mul (15 * (κ + 9)))).sub
      ((heat_derivative ν (κ + 25) 0).const_mul (5 * (κ + 25)))).const_mul (ν ^ 2 / 16))
  apply h.congr_deriv
  simp only [heat_zero]
  ring

theorem delayed_source_derivative (ν κ : ℝ) :
    HasDerivAt (fun t ↦ delayedRate ν κ t + ν * delayed ν κ t) (120 * ν ^ 3) 0 := by
  have h := (delayed_acceleration ν κ).add ((delayed_derivative ν κ 0).const_mul ν)
  change HasDerivAt (fun t ↦ delayedRate ν κ t + ν * delayed ν κ t) _ 0 at h
  simpa only [delayedRate_zero, mul_zero, add_zero] using h

theorem delayed_not_unforced (ν κ : ℝ) (hν : 0 < ν) :
    ¬ ∀ t, delayedRate ν κ t + ν * delayed ν κ t = 0 := by
  intro h
  have hf : (fun t ↦ delayedRate ν κ t + ν * delayed ν κ t) = fun _ ↦ 0 := funext h
  have hd := delayed_source_derivative ν κ
  rw [hf] at hd
  have he := hd.unique (hasDerivAt_const 0 (0 : ℝ))
  have hp : 0 < ν ^ 3 := pow_pos hν _
  linarith

end Mettapedia.FluidDynamics.NavierStokes.HeatGradientObserver
