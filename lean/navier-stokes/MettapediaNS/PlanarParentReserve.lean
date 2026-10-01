import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# A nonlinear planar parent reserve and signed replenishment

For a mean-zero planar parent vorticity, `Z`, `Y`, `W` denote its squared
L2 norm and the squared norms of its gradient and Laplacian. The analytic
periodic inequalities in the accompanying lab give `Z ≤ Y ≤ W`, strain
at most `4 * sqrt W`, and the derivative hypotheses below. The reserve
pays the strain of arbitrary interacting planar parents, not only heat
shears. The receiver reserve then pays absolute vertical stretching.

With actual three-dimensional fluctuations, the averaged parent and
receiver have Reynolds sources. Both signed source costs remain in the
certified inequality. Their original-datum payment is open. This module
certifies scalar calculus and absorption, not the PDE identification,
periodic Sobolev estimates or arbitrary-data regularity. The derivative
formula assumes `Y > 0`; the zero-vorticity passage is analytic.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PlanarParentReserve

open Set MeasureTheory

def parentReserve (ν Z Y : ℝ) : ℝ :=
  8 / ν * Real.sqrt Y * Real.exp (64 * Z / ν ^ 2)

def rateFactor (ν Z Y : ℝ) : ℝ :=
  4 * Real.exp (64 * Z / ν ^ 2) / (ν * Real.sqrt Y)

def parentRate (ν Z Y Z' Y' : ℝ) : ℝ :=
  rateFactor ν Z Y * (Y' + 128 * Y * Z' / ν ^ 2)

/-- `A = <omega,F>` and `B = <grad omega,grad F>` for the actual
averaged vorticity source. Neither sign is prescribed. -/
def feedback (ν Z Y A B : ℝ) : ℝ :=
  rateFactor ν Z Y * (2 * B + 256 * Y * A / ν ^ 2)

theorem parentReserve_nonneg (ν Z Y : ℝ) (hν : 0 < ν) :
    0 ≤ parentReserve ν Z Y := by
  unfold parentReserve
  positivity

theorem parentReserve_derivative (ν t : ℝ) (Z Y : ℝ → ℝ) (Z' Y' : ℝ)
    (hν : ν ≠ 0) (hY : 0 < Y t)
    (hZ' : HasDerivAt Z Z' t) (hY' : HasDerivAt Y Y' t) :
    HasDerivAt (fun s ↦ parentReserve ν (Z s) (Y s))
      (parentRate ν (Z t) (Y t) Z' Y') t := by
  have h := ((hY'.sqrt (ne_of_gt hY)).const_mul (8 / ν)).mul
    (((hZ'.const_mul 64).div_const (ν ^ 2)).exp)
  apply h.congr_deriv
  dsimp [parentRate, rateFactor]
  have hs : Real.sqrt (Y t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hY)
  field_simp
  rw [Real.sq_sqrt hY.le]
  ring

theorem feedback_eq (ν Z Y A B : ℝ) (hν : ν ≠ 0) (hY : 0 < Y) :
    feedback ν Z Y A B = parentReserve ν Z Y * (B / Y + 128 * A / ν ^ 2) := by
  unfold feedback rateFactor parentReserve
  have hs : Real.sqrt Y ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hY)
  field_simp
  rw [Real.sq_sqrt hY.le]
  ring

/-- The negative planar transport allowance is paid using `Z ≤ Y`.
Replenishment by the actual Reynolds source is retained explicitly. -/
theorem parent_payment_with_feedback (ν Z Y W Z' Y' A B : ℝ)
    (hν : 0 < ν) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hY : 0 < Y) (hYW : Y ≤ W)
    (hZ' : Z' = -2 * ν * Y + 2 * A)
    (hY' : Y' ≤ -ν * W + 256 * Z * Y / ν + 2 * B) :
    parentRate ν Z Y Z' Y' + 4 * Real.sqrt W ≤ feedback ν Z Y A B := by
  have hW : 0 ≤ W := hY.le.trans hYW
  have hν0 : ν ≠ 0 := ne_of_gt hν
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY
  have hsW : 0 ≤ Real.sqrt W := Real.sqrt_nonneg W
  have hsqY := Real.sq_sqrt hY.le
  have hsqW := Real.sq_sqrt hW
  have hroot := Real.sqrt_le_sqrt hYW
  have he : 1 ≤ Real.exp (64 * Z / ν ^ 2) := Real.one_le_exp (by positivity)
  have hinner : Y' + 128 * Y * Z' / ν ^ 2 ≤
      -ν * W + 2 * B + 256 * Y * A / ν ^ 2 := by
    rw [hZ']
    have hp := mul_nonneg hY.le (sub_nonneg.mpr hZY)
    have hi := (le_div_iff₀ hν).mp
      (show Y' + ν * W - 2 * B ≤ 256 * Z * Y / ν by linarith)
    refine le_of_mul_le_mul_right (a := ν ^ 2) ?_ (sq_pos_of_pos hν)
    field_simp
    nlinarith [mul_nonneg hν.le hp, mul_nonneg hν.le (sub_nonneg.mpr hi)]
  have hf : 0 ≤ rateFactor ν Z Y := by unfold rateFactor; positivity
  have hm := mul_le_mul_of_nonneg_left hinner hf
  have hrootprod : Real.sqrt W * Real.sqrt Y ≤ W := by
    nlinarith [mul_nonneg hsW (sub_nonneg.mpr hroot)]
  have hpaid : 4 * Real.sqrt W ≤ rateFactor ν Z Y * (ν * W) := by
    unfold rateFactor
    refine le_of_mul_le_mul_right (a := ν * Real.sqrt Y) ?_ (mul_pos hν hsY)
    field_simp
    nlinarith [mul_nonneg hW (sub_nonneg.mpr he)]
  unfold parentRate feedback
  nlinarith only [hm, hpaid]

theorem unforced_parent_payment (ν Z Y W Z' Y' : ℝ)
    (hν : 0 < ν) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hY : 0 < Y) (hYW : Y ≤ W)
    (hZ' : Z' = -2 * ν * Y)
    (hY' : Y' ≤ -ν * W + 256 * Z * Y / ν) :
    parentRate ν Z Y Z' Y' + 4 * Real.sqrt W ≤ 0 := by
  simpa [feedback] using parent_payment_with_feedback ν Z Y W Z' Y' 0 0
    hν hZ hZY hY hYW (by simpa using hZ') (by simpa using hY')

def receiverReserve (r E : ℝ) : ℝ := E * (Real.exp (2 * r) - 1)

theorem receiverReserve_nonneg (r E : ℝ) (hr : 0 ≤ r) (hE : 0 ≤ E) :
    0 ≤ receiverReserve r E := by
  unfold receiverReserve
  exact mul_nonneg hE (sub_nonneg.mpr (Real.one_le_exp (by positivity)))

theorem receiverReserve_derivative (r E : ℝ → ℝ) (t r' E' : ℝ)
    (hr : HasDerivAt r r' t) (hE : HasDerivAt E E' t) :
    HasDerivAt (fun s ↦ receiverReserve (r s) (E s))
      ((Real.exp (2 * r t) - 1) * E' + 2 * E t * Real.exp (2 * r t) * r') t := by
  have h := hE.mul ((((hr.const_mul 2).exp).sub_const 1))
  apply h.congr_deriv
  ring

/-- The signed parent source `J` and vertical source `C` are the complete
remaining bill. Dropping either would change the physical statement. -/
theorem receiver_payment_with_feedback (ν r E D G q J C r' E' : ℝ)
    (hr : 0 ≤ r) (hE : 0 ≤ E)
    (hG : |G| ≤ q * E) (hr' : r' + q ≤ J)
    (hE' : E' = 2 * G - 2 * ν * D + 2 * C) :
    (Real.exp (2 * r) - 1) * E' + 2 * E * Real.exp (2 * r) * r' +
      2 * |G| + 2 * ν * (Real.exp (2 * r) - 1) * D ≤
        2 * (Real.exp (2 * r) - 1) * C + 2 * E * Real.exp (2 * r) * J := by
  have he : 0 ≤ Real.exp (2 * r) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hg := mul_nonneg he (sub_nonneg.mpr (le_abs_self G))
  have hp := mul_nonneg (Real.exp_pos (2 * r)).le (sub_nonneg.mpr hG)
  have hj := mul_nonneg (mul_nonneg hE (Real.exp_pos (2 * r)).le)
    (sub_nonneg.mpr hr')
  rw [hE']
  nlinarith

theorem unforced_receiver_payment (ν r E D G q r' : ℝ)
    (hr : 0 ≤ r) (hE : 0 ≤ E) (hG : |G| ≤ q * E) (hr' : r' + q ≤ 0) :
    (Real.exp (2 * r) - 1) * (2 * G - 2 * ν * D) +
      2 * E * Real.exp (2 * r) * r' + 2 * |G| +
        2 * ν * (Real.exp (2 * r) - 1) * D ≤ 0 := by
  simpa using receiver_payment_with_feedback ν r E D G q 0 0 r'
    (2 * G - 2 * ν * D) hr hE hG hr' (by ring)

/-- Diffusion is nonnegative, so the same reserve pays the absolute
stretching itself, not only a difference with dissipation. -/
theorem unforced_absolute_payment (ν r E D G q r' : ℝ)
    (hν : 0 ≤ ν) (hr : 0 ≤ r) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hG : |G| ≤ q * E) (hr' : r' + q ≤ 0) :
    (Real.exp (2 * r) - 1) * (2 * G - 2 * ν * D) +
      2 * E * Real.exp (2 * r) * r' + 2 * |G| ≤ 0 := by
  have hp := unforced_receiver_payment ν r E D G q r' hr hE hG hr'
  have he : 0 ≤ Real.exp (2 * r) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by positivity))
  nlinarith [mul_nonneg (mul_nonneg hν he) hD]

/-- The same reserve is used at every seam. This integration theorem
retains the signed source instead of supplying its missing bound. -/
theorem interval_payment (R ρ cost source : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hR : ContinuousOn R (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt R (ρ t) t)
    (hρ : IntervalIntegrable ρ volume a b)
    (hc : IntervalIntegrable cost volume a b)
    (hs : IntervalIntegrable source volume a b)
    (hp : ∀ t ∈ Icc a b, ρ t + cost t ≤ source t) :
    (∫ t in a..b, cost t) ≤ R a - R b + ∫ t in a..b, source t := by
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hR hd hρ
  have hi := intervalIntegral.integral_mono_on hab (hρ.add hc) hs hp
  rw [intervalIntegral.integral_add hρ hc, hft] at hi
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PlanarParentReserve
