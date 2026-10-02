import MettapediaNS.HeatGradientObserver
import MettapediaNS.PlanarParentReserve

/-!
# A decaying cellular parent and its finite cycle reserve

The horizontal cellular field has an exact periodic pressure and no
external force. Its total advection clock is bounded by the original
amplitude divided by viscosity. The same remaining clock is retained
at every seam. The complete scalar gradient production admits the
usual exponential envelope, and the existing receiver reserve pays
absolute stretching under its explicit energy-law hypotheses.

The passive parabolic solution, the maximum-principle identification of
its gradient with the envelope, and the annular construction of arbitrary
finite approximate pattern cycles are analytic in the companion lab.
This module does not assert those existence or identification results.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.CellularCycleReserve

open MeasureTheory

def amplitude (A ν t : ℝ) : ℝ := A * Real.exp (-ν * t)
def remaining (A ν t : ℝ) : ℝ := amplitude A ν t / ν
def clock (A ν t : ℝ) : ℝ := A / ν - remaining A ν t

theorem amplitude_derivative (A ν t : ℝ) :
    HasDerivAt (amplitude A ν) (-ν * amplitude A ν t) t := by
  apply ((((hasDerivAt_id t).const_mul (-ν)).exp).const_mul A).congr_deriv
  dsimp [amplitude]
  ring

theorem amplitude_nonneg (A ν t : ℝ) (hA : 0 ≤ A) : 0 ≤ amplitude A ν t := by
  exact mul_nonneg hA (Real.exp_pos _).le

theorem remaining_nonneg (A ν t : ℝ) (hA : 0 ≤ A) (hν : 0 < ν) :
    0 ≤ remaining A ν t := div_nonneg (amplitude_nonneg A ν t hA) hν.le

theorem remaining_derivative (A ν t : ℝ) (hν : ν ≠ 0) :
    HasDerivAt (remaining A ν) (-amplitude A ν t) t := by
  apply ((amplitude_derivative A ν t).div_const ν).congr_deriv
  field_simp

theorem clock_derivative (A ν t : ℝ) (hν : ν ≠ 0) :
    HasDerivAt (clock A ν) (amplitude A ν t) t := by
  unfold clock
  simpa only [neg_neg] using (remaining_derivative A ν t hν).const_sub (A / ν)

@[simp] theorem clock_zero (A ν : ℝ) : clock A ν 0 = 0 := by
  simp [clock, remaining, amplitude]

theorem clock_nonneg (A ν t : ℝ) (hA : 0 ≤ A) (hν : 0 < ν) (ht : 0 ≤ t) :
    0 ≤ clock A ν t := by
  have he : Real.exp (-ν * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have ha : amplitude A ν t ≤ A := by
    simpa [amplitude] using mul_le_mul_of_nonneg_left he hA
  exact sub_nonneg.mpr ((div_le_div_iff_of_pos_right hν).mpr ha)

theorem clock_le (A ν t : ℝ) (hA : 0 ≤ A) (hν : 0 < ν) :
    clock A ν t ≤ A / ν := sub_le_self _ (remaining_nonneg A ν t hA hν)

theorem clock_lt (A ν t : ℝ) (hA : 0 < A) (hν : 0 < ν) :
    clock A ν t < A / ν := by
  exact sub_lt_self _ (div_pos (mul_pos hA (Real.exp_pos _)) hν)

/-- Every segment uses the original clock; its remaining stock is not reset. -/
theorem seam_payment (A ν a b : ℝ) :
    clock A ν b - clock A ν a = remaining A ν a - remaining A ν b := by
  unfold clock
  ring

theorem integral_amplitude (A ν T : ℝ) (hν : ν ≠ 0) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, amplitude A ν t) = clock A ν T := by
  have hc : Continuous (clock A ν) := by unfold clock remaining amplitude; fun_prop
  have hi : IntervalIntegrable (amplitude A ν) MeasureTheory.volume 0 T :=
    (show Continuous (amplitude A ν) by unfold amplitude; fun_prop).intervalIntegrable 0 T
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hc.continuousOn
    (fun t _ ↦ clock_derivative A ν t hν) hi
  simpa only [clock_zero, sub_zero] using h

theorem integral_amplitude_le (A ν T : ℝ) (hA : 0 ≤ A) (hν : 0 < ν) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, amplitude A ν t) ≤ A / ν := by
  rw [integral_amplitude A ν T (ne_of_gt hν) hT]
  exact clock_le A ν T hA hν

theorem finite_turn_count (A ν t P : ℝ) (n : ℕ)
    (hA : 0 < A) (hν : 0 < ν) (hP : 0 < P)
    (hn : (n : ℝ) * P ≤ clock A ν t) : (n : ℝ) < A / (ν * P) := by
  have h := hn.trans_lt (clock_lt A ν t hA hν)
  rw [div_mul_eq_div_div]
  exact (lt_div_iff₀ hP).mpr h

def horizontalX (A ν t _x y : ℝ) : ℝ := amplitude A ν t * Real.sin y
def horizontalY (A ν t x _y : ℝ) : ℝ := -(amplitude A ν t * Real.sin x)
def pressure (A ν t x y : ℝ) : ℝ :=
  -(amplitude A ν t)^2 * Real.cos x * Real.cos y

theorem horizontalX_y (A ν t x y : ℝ) :
    deriv (horizontalX A ν t x) y = amplitude A ν t * Real.cos y := by
  exact ((Real.hasDerivAt_sin y).const_mul (amplitude A ν t)).deriv

theorem horizontalY_x (A ν t x y : ℝ) :
    deriv (fun s ↦ horizontalY A ν t s y) x = -amplitude A ν t * Real.cos x := by
  have h := (((Real.hasDerivAt_sin x).const_mul (amplitude A ν t)).neg).deriv
  have he : (-fun s ↦ amplitude A ν t * Real.sin s) =
      (fun s ↦ horizontalY A ν t s y) := by
    funext s
    rfl
  rw [he] at h
  simpa only [neg_mul] using h

theorem horizontal_divergence (A ν t x y : ℝ) :
    deriv (fun s ↦ horizontalX A ν t s y) x +
      deriv (horizontalY A ν t x) y = 0 := by
  change deriv (fun _ : ℝ ↦ amplitude A ν t * Real.sin y) x +
    deriv (fun _ : ℝ ↦ -(amplitude A ν t * Real.sin x)) y = 0
  simp

theorem horizontalX_time (A ν t x y : ℝ) :
    deriv (fun s ↦ horizontalX A ν s x y) t = -ν * horizontalX A ν t x y := by
  have h := ((amplitude_derivative A ν t).mul_const (Real.sin y)).deriv
  change deriv (fun s ↦ amplitude A ν s * Real.sin y) t = _
  rw [h]
  unfold horizontalX
  ring

theorem horizontalY_time (A ν t x y : ℝ) :
    deriv (fun s ↦ horizontalY A ν s x y) t = -ν * horizontalY A ν t x y := by
  have h := (((amplitude_derivative A ν t).mul_const (Real.sin x)).neg).deriv
  have he : (-fun s ↦ amplitude A ν s * Real.sin x) =
      (fun s ↦ horizontalY A ν s x y) := by
    funext s
    rfl
  rw [he] at h
  rw [h]
  unfold horizontalY
  ring

theorem horizontalX_yy (A ν t x y : ℝ) :
    deriv (fun s ↦ deriv (horizontalX A ν t x) s) y = -horizontalX A ν t x y := by
  simp only [horizontalX_y]
  rw [((Real.hasDerivAt_cos y).const_mul (amplitude A ν t)).deriv]
  unfold horizontalX
  ring

theorem horizontalY_xx (A ν t x y : ℝ) :
    deriv (fun s ↦ deriv (fun r ↦ horizontalY A ν t r y) s) x =
      -horizontalY A ν t x y := by
  simp only [horizontalY_x]
  rw [((Real.hasDerivAt_cos x).const_mul (-amplitude A ν t)).deriv]
  unfold horizontalY
  ring

theorem pressure_x (A ν t x y : ℝ) :
    deriv (fun s ↦ pressure A ν t s y) x =
      (amplitude A ν t)^2 * Real.sin x * Real.cos y := by
  have h := (((Real.hasDerivAt_cos x).const_mul (-(amplitude A ν t)^2)).mul_const
    (Real.cos y)).deriv
  change deriv (fun s ↦ -(amplitude A ν t)^2 * Real.cos s * Real.cos y) x = _
  rw [h]
  ring

theorem pressure_y (A ν t x y : ℝ) :
    deriv (pressure A ν t x) y =
      (amplitude A ν t)^2 * Real.cos x * Real.sin y := by
  change deriv (fun s ↦ -(amplitude A ν t)^2 * Real.cos x * Real.cos s) y = _
  rw [((Real.hasDerivAt_cos y).const_mul (-(amplitude A ν t)^2 * Real.cos x)).deriv]
  ring

/-- The literal first horizontal equation, including its pressure and diffusion. -/
theorem horizontal_unforced_x (A ν t x y : ℝ) :
    deriv (fun s ↦ horizontalX A ν s x y) t +
      horizontalX A ν t x y * deriv (fun s ↦ horizontalX A ν t s y) x +
      horizontalY A ν t x y * deriv (horizontalX A ν t x) y +
      deriv (fun s ↦ pressure A ν t s y) x =
    ν * (deriv (fun s ↦ deriv (fun r ↦ horizontalX A ν t r y) s) x +
      deriv (fun s ↦ deriv (horizontalX A ν t x) s) y) := by
  rw [horizontalX_time, horizontalX_y, pressure_x, horizontalX_yy]
  dsimp only [horizontalX, horizontalY]
  simp
  ring

theorem horizontal_unforced_y (A ν t x y : ℝ) :
    deriv (fun s ↦ horizontalY A ν s x y) t +
      horizontalX A ν t x y * deriv (fun s ↦ horizontalY A ν t s y) x +
      horizontalY A ν t x y * deriv (horizontalY A ν t x) y +
      deriv (pressure A ν t x) y =
    ν * (deriv (fun s ↦ deriv (fun r ↦ horizontalY A ν t r y) s) x +
      deriv (fun s ↦ deriv (horizontalY A ν t x) s) y) := by
  rw [horizontalY_time, horizontalY_x, pressure_y, horizontalY_xx]
  have hc : deriv (horizontalY A ν t x) = fun _ ↦ 0 := by
    funext y
    change deriv (fun _ : ℝ ↦ -(amplitude A ν t * Real.sin x)) y = 0
    simp
  rw [hc]
  dsimp only [horizontalX, horizontalY]
  simp
  ring

def gradientEnvelope (G A ν t : ℝ) : ℝ := G * Real.exp (clock A ν t)

theorem gradientEnvelope_derivative (G A ν t : ℝ) (hν : ν ≠ 0) :
    HasDerivAt (gradientEnvelope G A ν)
      (amplitude A ν t * gradientEnvelope G A ν t) t := by
  apply (((clock_derivative A ν t hν).exp).const_mul G).congr_deriv
  unfold gradientEnvelope
  ring

theorem gradientEnvelope_le (G A ν t : ℝ) (hG : 0 ≤ G)
    (hA : 0 ≤ A) (hν : 0 < ν) :
    gradientEnvelope G A ν t ≤ G * Real.exp (A / ν) := by
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (clock_le A ν t hA hν)) hG

/-- The complete reaction in the differentiated passive equation, after
moving transport and scalar diffusion to the left. -/
def gradientProduction (a ν x y gx gy hxx hxy hyy : ℝ) : ℝ :=
  -2 * a * (Real.cos y - Real.cos x) * gx * gy -
    2 * ν * (hxx^2 + 2*hxy^2 + hyy^2)

theorem gradientProduction_le (a ν x y gx gy hxx hxy hyy : ℝ)
    (ha : 0 ≤ a) (hν : 0 ≤ ν) :
    gradientProduction a ν x y gx gy hxx hxy hyy ≤ 2*a*(gx^2+gy^2) := by
  have hp : 0 ≤ (2 + (Real.cos y - Real.cos x)) * (gx + gy)^2 :=
    mul_nonneg (by linarith [Real.neg_one_le_cos y, Real.cos_le_one x]) (sq_nonneg _)
  have hm : 0 ≤ (2 - (Real.cos y - Real.cos x)) * (gx - gy)^2 :=
    mul_nonneg (by linarith [Real.cos_le_one y, Real.neg_one_le_cos x]) (sq_nonneg _)
  have hr : -(Real.cos y - Real.cos x)*gx*gy ≤ gx^2+gy^2 := by
    nlinarith only [hp, hm]
  have hd : 0 ≤ 2*ν*(hxx^2+2*hxy^2+hyy^2) := by positivity
  have hb := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*a by positivity)
  unfold gradientProduction
  nlinarith only [hb, hd]

/-- A finite original parent stock pays the receiver without a refill.
The physical receiver-energy identification is stated separately in the lab. -/
theorem receiver_payment (A ν t E D G : ℝ) (hA : 0 ≤ A) (hν : 0 < ν)
    (hE : 0 ≤ E) (hD : 0 ≤ D) (hG : |G| ≤ amplitude A ν t * E) :
    (Real.exp (2 * remaining A ν t) - 1) * (2*G - 2*ν*D) +
      2*E*Real.exp (2 * remaining A ν t) * (-amplitude A ν t) +
      2*|G| ≤ 0 := by
  exact PlanarParentReserve.unforced_absolute_payment ν (remaining A ν t) E D G
    (amplitude A ν t) (-amplitude A ν t) hν.le
    (remaining_nonneg A ν t hA hν) hE hD hG (by linarith)

end Mettapedia.FluidDynamics.NavierStokes.CellularCycleReserve
