import MettapediaNS.PairCycleHistory

/-!
# First reciprocal stretching history at unequal parent scales

The exact Fourier recurrence in `labs/anisotropic_pair_history.py` identifies
the formula below with the sixth mixed amplitude coefficient of physical
stretching, after subtracting all three complete two-parent evolutions.
Here `a`, `b`, `c` are the positive squared parent frequencies, and time is
the viscous clock. The formula has a favorable sign for every such scale
triple, without comparable-frequency or small-time assumptions.

This module certifies the scalar sign and its finite nonnegative sums.
Identification with NS solution-map derivatives, and the extension from
Fourier polynomials to smooth separated profiles, remain analytic. It does
not control the higher coefficients or their sum for arbitrary initial data.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.AnisotropicCycleHistory

open Set MeasureTheory

/-- The remainder after degree three of `(1 - slope*t) * exp(rate*t)`. -/
def remainder (slope rate t : ℝ) : ℝ :=
  (1 - slope * t) * Real.exp (rate * t) - 1 - (rate - slope) * t -
    (rate ^ 2 - 2 * slope * rate) * t ^ 2 / 2 -
    (rate ^ 3 - 3 * slope * rate ^ 2) * t ^ 3 / 6

private def first (slope rate t : ℝ) : ℝ :=
  (rate - slope - slope * rate * t) * Real.exp (rate * t) - (rate - slope) -
    (rate ^ 2 - 2 * slope * rate) * t -
    (rate ^ 3 - 3 * slope * rate ^ 2) * t ^ 2 / 2

private def second (slope rate t : ℝ) : ℝ :=
  (rate ^ 2 - 2 * slope * rate - slope * rate ^ 2 * t) * Real.exp (rate * t) -
    (rate ^ 2 - 2 * slope * rate) - (rate ^ 3 - 3 * slope * rate ^ 2) * t

private def third (slope rate t : ℝ) : ℝ :=
  (rate ^ 3 - 3 * slope * rate ^ 2 - slope * rate ^ 3 * t) *
    Real.exp (rate * t) - (rate ^ 3 - 3 * slope * rate ^ 2)

private theorem exp_derivative (rate t : ℝ) :
    HasDerivAt (fun t ↦ Real.exp (rate * t))
      (rate * Real.exp (rate * t)) t := by
  apply (((hasDerivAt_id t).const_mul rate).exp).congr_deriv
  dsimp
  ring

private theorem remainder_derivative (slope rate t : ℝ) :
    HasDerivAt (remainder slope rate) (first slope rate t) t := by
  have h := (((((hasDerivAt_const t 1).sub ((hasDerivAt_id t).const_mul slope)).mul
    (exp_derivative rate t)).sub_const 1).sub
    ((hasDerivAt_id t).const_mul (rate - slope))).sub
    ((((hasDerivAt_id t).pow 2).const_mul (rate ^ 2 - 2 * slope * rate)).div_const 2)
  have h' := h.sub
    ((((hasDerivAt_id t).pow 3).const_mul (rate ^ 3 - 3 * slope * rate ^ 2)).div_const 6)
  apply h'.congr_deriv
  dsimp [first]; ring

private theorem first_derivative (slope rate t : ℝ) :
    HasDerivAt (first slope rate) (second slope rate t) t := by
  have h := (((((hasDerivAt_const t (rate - slope)).sub
    ((hasDerivAt_id t).const_mul (slope * rate))).mul (exp_derivative rate t)).sub_const
    (rate - slope)).sub ((hasDerivAt_id t).const_mul (rate ^ 2 - 2 * slope * rate))).sub
    ((((hasDerivAt_id t).pow 2).const_mul (rate ^ 3 - 3 * slope * rate ^ 2)).div_const 2)
  apply h.congr_deriv
  dsimp [second]; ring

private theorem second_derivative (slope rate t : ℝ) :
    HasDerivAt (second slope rate) (third slope rate t) t := by
  have h := ((((hasDerivAt_const t (rate ^ 2 - 2 * slope * rate)).sub
    ((hasDerivAt_id t).const_mul (slope * rate ^ 2))).mul (exp_derivative rate t)).sub_const
    (rate ^ 2 - 2 * slope * rate)).sub
    ((hasDerivAt_id t).const_mul (rate ^ 3 - 3 * slope * rate ^ 2))
  apply h.congr_deriv
  dsimp [third]; ring

private theorem third_derivative (slope rate t : ℝ) :
    HasDerivAt (third slope rate)
      (rate ^ 3 * (rate - 4 * slope - slope * rate * t) * Real.exp (rate * t)) t := by
  have h := (((hasDerivAt_const t (rate ^ 3 - 3 * slope * rate ^ 2)).sub
    ((hasDerivAt_id t).const_mul (slope * rate ^ 3))).mul
    (exp_derivative rate t)).sub_const (rate ^ 3 - 3 * slope * rate ^ 2)
  apply h.congr_deriv
  dsimp; ring

private theorem nonpos_from_zero {f g : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt f (g t) t) (h0 : f 0 = 0)
    (hg : ∀ t, 0 ≤ t → g t ≤ 0) (t : ℝ) (ht : 0 ≤ t) : f t ≤ 0 := by
  have hm : AntitoneOn f (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun r _ ↦ (hd r).continuousAt.continuousWithinAt) (f' := g)
    · intro r _; exact (hd r).hasDerivWithinAt
    · intro r hr; exact hg r (interior_subset hr)
  have h := hm (show (0 : ℝ) ∈ Ici 0 from by simp) ht ht
  simpa only [h0] using h

theorem remainder_nonpos (slope rate t : ℝ) (hs : 0 ≤ slope)
    (hr : 0 ≤ rate) (hbound : rate ≤ 4 * slope) (ht : 0 ≤ t) :
    remainder slope rate t ≤ 0 := by
  have h3 : ∀ r, 0 ≤ r → third slope rate r ≤ 0 := by
    intro r hrt
    apply nonpos_from_zero (third_derivative slope rate)
      (by simp [third]) ?_ r hrt
    intro x hx
    have hp := mul_nonneg (mul_nonneg hs hr) hx
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hr 3) (by linarith))
      (Real.exp_pos _).le
  have h2 := nonpos_from_zero (second_derivative slope rate)
    (by simp [second]) h3
  have h1 := nonpos_from_zero (first_derivative slope rate)
    (by simp [first]) h2
  exact nonpos_from_zero (remainder_derivative slope rate)
    (by simp [remainder]) h1 t ht

def weight (a b c : ℝ) : ℝ := 3 * a * b ^ 2 / (32 * c ^ 2 * (a + b + c))

theorem weight_pos (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < weight a b c := by unfold weight; positivity

/-- Signed form of the complete coefficient, retaining the three scale orderings. -/
def sixthStretch (a b c t : ℝ) : ℝ :=
  Real.exp (-2 * (a + b + c) * t) *
    (-a * b * c / 4 * t ^ 3 +
      weight a b c * remainder (2 * (a + b + c) / 3) (2 * c) t +
      weight b c a * remainder (2 * (a + b + c) / 3) (2 * a) t +
      weight c a b * remainder (2 * (a + b + c) / 3) (2 * b) t)

theorem sixth_le_cubic (a b c t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : 0 ≤ t) :
    sixthStretch a b c t ≤
      Real.exp (-2 * (a + b + c) * t) * (-a * b * c / 4 * t ^ 3) := by
  have hs : 0 ≤ 2 * (a + b + c) / 3 := by positivity
  have ha' := remainder_nonpos (2 * (a + b + c) / 3) (2 * a) t hs
    (by positivity) (by linarith) ht
  have hb' := remainder_nonpos (2 * (a + b + c) / 3) (2 * b) t hs
    (by positivity) (by linarith) ht
  have hc' := remainder_nonpos (2 * (a + b + c) / 3) (2 * c) t hs
    (by positivity) (by linarith) ht
  have hwa := mul_nonpos_of_nonneg_of_nonpos (weight_pos b c a hb hc ha).le ha'
  have hwb := mul_nonpos_of_nonneg_of_nonpos (weight_pos c a b hc ha hb).le hb'
  have hwc := mul_nonpos_of_nonneg_of_nonpos (weight_pos a b c ha hb hc).le hc'
  unfold sixthStretch
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  linarith only [hwa, hwb, hwc]

theorem sixth_nonpos (a b c t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : 0 ≤ t) : sixthStretch a b c t ≤ 0 := by
  apply (sixth_le_cubic a b c t ha hb hc ht).trans
  have h := mul_nonneg (by positivity : 0 ≤ a * b * c / 4) (pow_nonneg ht 3)
  apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
  nlinarith only [h]

theorem sixth_neg (a b c t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : 0 < t) : sixthStretch a b c t < 0 := by
  apply lt_of_le_of_lt (sixth_le_cubic a b c t ha hb hc ht.le)
  have h := mul_pos (by positivity : 0 < a * b * c / 4) (pow_pos ht 3)
  apply mul_neg_of_pos_of_neg (Real.exp_pos _)
  nlinarith only [h]

theorem sixth_interval_payment (a b c s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hs : 0 ≤ s) (hst : s ≤ t) :
    2 * (∫ r in s..t, sixthStretch a b c r) ≤ 0 := by
  have hi : 0 ≤ (∫ r in s..t, -sixthStretch a b c r) := by
    apply intervalIntegral.integral_nonneg hst
    intro r hr
    exact neg_nonneg.mpr (sixth_nonpos a b c r ha hb hc (hs.trans hr.1))
  rw [intervalIntegral.integral_neg] at hi
  linarith only [hi]

theorem sixth_unit (t : ℝ) :
    sixthStretch 1 1 1 t = PairCycleHistory.sixthStretch t := by
  have he : Real.exp (-6 * t) = Real.exp (-2 * t) ^ 3 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hp : Real.exp (-2 * t) ^ 3 * Real.exp (2 * t) = Real.exp (-2 * t) ^ 2 := by
    calc
      _ = Real.exp (-2 * t) ^ 2 * (Real.exp (-2 * t) * Real.exp (2 * t)) := by ring
      _ = _ := by rw [← Real.exp_add]; ring_nf; simp
  unfold sixthStretch weight remainder PairCycleHistory.sixthStretch
    PairCycleHistory.rateShape PairCycleHistory.heat
  norm_num
  simp only [neg_mul] at he hp
  rw [he]
  linear_combination ((3 / 32 : ℝ) * (1 - 2 * t)) * hp

/-- The scalar sign survives finite Fourier mixtures with nonnegative spectral weights. -/
theorem finite_profile_nonpos {ι : Type*} (S : Finset ι)
    (amplitude a b c : ι → ℝ) (t : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ amplitude i) (ha : ∀ i ∈ S, 0 < a i)
    (hb : ∀ i ∈ S, 0 < b i) (hc : ∀ i ∈ S, 0 < c i) (ht : 0 ≤ t) :
    (∑ i ∈ S, amplitude i * sixthStretch (a i) (b i) (c i) t) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  exact mul_nonpos_of_nonneg_of_nonpos (hw i hi)
    (sixth_nonpos (a i) (b i) (c i) t (ha i hi) (hb i hi) (hc i hi) ht)

end Mettapedia.FluidDynamics.NavierStokes.AnisotropicCycleHistory
