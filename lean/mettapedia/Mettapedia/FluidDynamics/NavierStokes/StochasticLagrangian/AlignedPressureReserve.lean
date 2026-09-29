import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# A joint reserve for aligned pressure, strain and vorticity

The analytic compact-swirl calculation in `labs/compressed_parent.py`
gives the following leading scalar rates at the initial time of actual
unforced flows. Writing physical vorticity magnitude as `Ω = w⁷`, they are

* `w' = σ w / 7`,
* `σ' = -(5/14) σ² - w¹⁴/10 + h`,
* `h' = -7 σ h - γ h`.

Here `h` is the negative axial pressure excess over an actual reference
flow. Finite packet width and the compact background cutoff give an
explicit additional initial pressure rate. The geometry is not an
invariant class of Navier--Stokes solutions.

This file proves a positive reserve for the stated scalar rates with
arbitrary signed defects, its physical-vorticity comparison and its
endpoint-retaining integral law. The gradient algebra also records why
an ODE certificate does not automatically extend to spatial diffusion.
Positivity of the physical pressure variable, the all-time rate defects,
and their signed cost for arbitrary fluid histories remain obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.AlignedPressureReserve

open MeasureTheory

def reserve (w σ h : ℝ) : ℝ := w ^ 5 * (2090 * σ ^ 2 + 154 * w ^ 14 + 665 * h)

def amplitudeRate (w σ fw : ℝ) : ℝ := σ * w / 7 + fw

def strainRate (w σ h fσ : ℝ) : ℝ := -(5/14) * σ ^ 2 - w ^ 14 / 10 + h + fσ

def pressureRate (γ σ h fh : ℝ) : ℝ := -7 * σ * h - γ * h + fh

/-- The ordinary differential of the polynomial reserve. -/
def differential (w σ h dw dσ dh : ℝ) : ℝ :=
  (10450 * w ^ 4 * σ ^ 2 + 2926 * w ^ 18 + 3325 * w ^ 4 * h) * dw +
    4180 * w ^ 5 * σ * dσ + 665 * w ^ 5 * dh

def damping (γ w h : ℝ) : ℝ := 665 * γ * w ^ 5 * h

def defectWork (w σ h fw fσ fh : ℝ) : ℝ := differential w σ h fw fσ fh

def production (γ w σ h fw fσ fh : ℝ) : ℝ :=
  differential w σ h (amplitudeRate w σ fw) (strainRate w σ h fσ)
    (pressureRate γ σ h fh)

theorem production_eq (γ w σ h fw fσ fh : ℝ) :
    production γ w σ h fw fσ fh = -damping γ w h + defectWork w σ h fw fσ fh := by
  dsimp [production, differential, amplitudeRate, strainRate, pressureRate, damping, defectWork]
  ring

theorem reserve_nonneg (w σ h : ℝ) (hw : 0 ≤ w) (hh : 0 ≤ h) :
    0 ≤ reserve w σ h := by
  unfold reserve
  positivity

/-- The reserve controls physical vorticity, not only a transported metric. -/
theorem coercive (w σ h : ℝ) (hw : 0 ≤ w) (hh : 0 ≤ h) :
    154 * w ^ 19 ≤ reserve w σ h := by
  have hn : 0 ≤ w ^ 5 * (2090 * σ ^ 2 + 665 * h) := by positivity
  have he : reserve w σ h = 154 * w ^ 19 + w ^ 5 * (2090 * σ ^ 2 + 665 * h) := by
    unfold reserve
    ring
  rw [he]
  linarith

/-- A coarse polynomial comparison avoids taking a fractional power.
In the physical application the vorticity magnitude is `w⁷`. -/
theorem physical_le (w σ h : ℝ) (hw : 0 ≤ w) (hh : 0 ≤ h) :
    w ^ 7 ≤ 1 + reserve w σ h / 154 := by
  have hn := reserve_nonneg w σ h hw hh
  by_cases hw1 : w ≤ 1
  · have hp : w ^ 7 ≤ 1 := pow_le_one₀ hw hw1
    have hq : 0 ≤ reserve w σ h / 154 := by positivity
    linarith
  · have hp : w ^ 7 ≤ w ^ 19 := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hw1)) (by omega)
    have hc := coercive w σ h hw hh
    linarith

theorem damping_nonneg (γ w h : ℝ) (hγ : 0 ≤ γ) (hw : 0 ≤ w) (hh : 0 ≤ h) :
    0 ≤ damping γ w h := by
  unfold damping
  positivity

/-- The actual initial finite-width correction in the compact aligned
compression test is favorable under the stated cutoff condition. This
does not claim that those geometric inequalities persist in time. -/
theorem compact_initial_production_nonpos (γ w σ h κ δ : ℝ)
    (hγ : 0 ≤ γ) (hw : 0 ≤ w) (hσ : σ ≤ 0) (hh : 0 ≤ h) (hδ : δ ≤ 36 * κ) :
    production γ w σ h 0 0 ((18 * κ - δ / 2) * σ * h) ≤ 0 := by
  have hk : 0 ≤ 18 * κ - δ / 2 := by linarith
  have hf : (18 * κ - δ / 2) * σ * h ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hk hσ) hh
  have hd := damping_nonneg γ w h hγ hw hh
  have hw5 : 0 ≤ 665 * w ^ 5 := by positivity
  have he := mul_nonpos_of_nonneg_of_nonpos hw5 hf
  rw [production_eq]
  simpa only [defectWork, differential, mul_zero, add_zero, zero_add] using
    (show -damping γ w h + 665 * w ^ 5 * ((18 * κ - δ / 2) * σ * h) ≤ 0 by linarith)

/-- The prior mixed-axis, unequal-width physical test has `σ=0`,
`h=7/4`, `h'=23γ`, and zero initial vorticity rate. Its pressure defect
is `99γ/4`. Thus even this joint observed reserve may initially grow.
The actual NS realization is the analytic test in `swirl_pressure_history.py`. -/
theorem unequal_parent_production (γ w : ℝ) :
    production γ w 0 (7/4) 0 0 ((99/4) * γ) = 15295 * γ * w ^ 5 := by
  dsimp [production, differential, amplitudeRate, strainRate, pressureRate]
  ring

/-- This is the derivative of the actual composed scalar function. -/
theorem hasDerivAt_reserve (w σ h : ℝ → ℝ) (dw dσ dh t : ℝ)
    (hw : HasDerivAt w dw t) (hσ : HasDerivAt σ dσ t) (hh : HasDerivAt h dh t) :
    HasDerivAt (fun s ↦ reserve (w s) (σ s) (h s))
      (differential (w t) (σ t) (h t) dw dσ dh) t := by
  have hr := (hw.pow 5).mul
    ((((hσ.pow 2).const_mul 2090).add ((hw.pow 14).const_mul 154)).add (hh.const_mul 665))
  convert! hr using 1
  simp only [differential, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub]
  ring

/-- The endpoint reserve is retained, so adjacent histories do not receive
a fresh initial allowance. No sign has been discarded from `defectWork`. -/
theorem interval_balance (a b : ℝ) (hab : a ≤ b) (w σ h γ fw fσ fh : ℝ → ℝ)
    (hw : ∀ t ∈ Set.Icc a b, HasDerivAt w (amplitudeRate (w t) (σ t) (fw t)) t)
    (hσ : ∀ t ∈ Set.Icc a b, HasDerivAt σ (strainRate (w t) (σ t) (h t) (fσ t)) t)
    (hh : ∀ t ∈ Set.Icc a b, HasDerivAt h (pressureRate (γ t) (σ t) (h t) (fh t)) t)
    (hiD : IntervalIntegrable (fun t ↦ damping (γ t) (w t) (h t)) volume a b)
    (hiF : IntervalIntegrable (fun t ↦ defectWork (w t) (σ t) (h t) (fw t) (fσ t) (fh t))
      volume a b) :
    reserve (w b) (σ b) (h b) + (∫ t in a..b, damping (γ t) (w t) (h t)) =
      reserve (w a) (σ a) (h a) +
        (∫ t in a..b, defectWork (w t) (σ t) (h t) (fw t) (fσ t) (fh t)) := by
  have heq : (∫ t in a..b, -damping (γ t) (w t) (h t) +
      defectWork (w t) (σ t) (h t) (fw t) (fσ t) (fh t)) =
      reserve (w b) (σ b) (h b) - reserve (w a) (σ a) (h a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hiD.neg.add hiF)
    intro t ht
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using ht
    have hd := hasDerivAt_reserve w σ h _ _ _ t (hw t ht') (hσ t ht') (hh t ht')
    change HasDerivAt _ (production (γ t) (w t) (σ t) (h t) (fw t) (fσ t) (fh t)) t at hd
    rwa [production_eq] at hd
  have hiNeg : IntervalIntegrable (fun t ↦ -damping (γ t) (w t) (h t)) volume a b := hiD.neg
  rw [intervalIntegral.integral_add hiNeg hiF, intervalIntegral.integral_neg] at heq
  linarith

/-- A finite signed defect allowance supplies a physical-vorticity bound.
The bound on that allowance for actual NS histories is not asserted here. -/
theorem physical_le_of_balance (wa σa ha wb σb hb dissipation work allowance : ℝ)
    (hwb : 0 ≤ wb) (hhb : 0 ≤ hb) (hd : 0 ≤ dissipation) (hf : work ≤ allowance)
    (heq : reserve wb σb hb + dissipation = reserve wa σa ha + work) :
    wb ^ 7 ≤ 1 + (reserve wa σa ha + allowance) / 154 := by
  have hp := physical_le wb σb hb hwb hhb
  linarith

/-- The same leading feedback has a reciprocal pressure/vorticity history.
Both rate defects remain, so the product is not silently conserved in NS. -/
theorem reciprocal_production (γ w σ h fw fh : ℝ) :
    49 * h * w ^ 48 * amplitudeRate w σ fw + w ^ 49 * pressureRate γ σ h fh =
      -γ * h * w ^ 49 + 49 * h * w ^ 48 * fw + w ^ 49 * fh := by
  unfold amplitudeRate pressureRate
  ring

/-- Substitution of a directional physical pressure Hessian `p`.
This algebra does not establish the physical identification of `h`. -/
theorem pressure_form (w σ p : ℝ) :
    reserve w σ (-p - (9/14) * σ ^ 2 + w ^ 14 / 10) =
      w ^ 5 * ((3325/2) * σ ^ 2 + (441/2) * w ^ 14 - 665 * p) := by
  unfold reserve
  ring

/-- In a planar flow the vorticity direction has zero strain and zero
directional pressure Hessian. The reserve reduces to a convex vorticity
power. Its physical realization and maximum principle are analytic. -/
theorem planar_reduction (w : ℝ) :
    reserve w 0 (w ^ 14 / 10) = (441/2) * w ^ 19 := by
  unfold reserve
  ring

/-- Hessian quadratic form of the reserve on one spatial derivative. -/
def secondDifferential (w σ h dw dσ dh : ℝ) : ℝ :=
  (41800 * w ^ 3 * σ ^ 2 + 52668 * w ^ 17 + 13300 * w ^ 3 * h) * dw ^ 2 +
    41800 * w ^ 4 * σ * dw * dσ + 6650 * w ^ 4 * dw * dh + 4180 * w ^ 5 * dσ ^ 2

/-- Remaining diffusion work when `DΩ=σΩ` and `w=Ω^(1/7)`.
The favorable vorticity-direction loss is separate. Sum over coordinates
and multiply by viscosity in the parabolic chain rule. -/
def gradientWork (w σ h dw dσ dh : ℝ) : ℝ :=
  (20900 * w ^ 3 * σ ^ 2 - 35112 * w ^ 17 + 6650 * w ^ 3 * h) * dw ^ 2 -
    41800 * w ^ 4 * σ * dw * dσ - 6650 * w ^ 4 * dw * dh - 4180 * w ^ 5 * dσ ^ 2

theorem gradientWork_eq (w σ h dw dσ dh : ℝ) (hw : w ≠ 0) :
    differential w σ h (6 * dw ^ 2 / w) 0 0 - secondDifferential w σ h dw dσ dh =
      gradientWork w σ h dw dσ dh := by
  unfold differential secondDifferential gradientWork
  field_simp
  ring

/-- Actual planar pressure identification correlates the spatial jets:
`h=Ω²/10=w¹⁴/10`. Its parabolic rate supplies the negative first term.
After that term is included, diffusion of the joint reserve is favorable. -/
theorem planar_gradient_balance (w dw : ℝ) :
    665 * w ^ 5 * (-(49/5) * w ^ 12 * dw ^ 2) +
      gradientWork w 0 (w ^ 14 / 10) dw 0 ((7/5) * w ^ 13 * dw) =
        -50274 * w ^ 17 * dw ^ 2 := by
  unfold gradientWork
  ring

/-- Scalar jets at which the reserve has zero spatial first derivative. -/
theorem stationary_scalar_jet : differential 1 0 1 1 0 (-6251/665) = 0 := by
  norm_num [differential]

/-- At the same jets the diffusion contribution is positive. This is an
algebraic obstruction to an automatic parabolic extension, not a claim
that these freely supplied jets are realized by an NS pressure. -/
theorem positive_scalar_diffusion : gradientWork 1 0 1 1 0 (-6251/665) = 34048 := by
  norm_num [gradientWork]

theorem scalar_diffusion_exceeds_damping :
    -damping 1 1 1 + gradientWork 1 0 1 1 0 (-6251/665) = 33383 := by
  rw [positive_scalar_diffusion]
  norm_num [damping]

end Mettapedia.FluidDynamics.NavierStokes.AlignedPressureReserve
