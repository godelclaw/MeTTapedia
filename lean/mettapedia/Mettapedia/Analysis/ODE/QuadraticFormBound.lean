/-
SPDX-License-Identifier: Apache-2.0
Adapted from OpenAI, NavierStokesAndEuler, NavierStokes/ViscousPropagator.lean.
Upstream revision: 8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538.
Modified by MeTTapedia contributors: extracted the Hilbert-space estimates,
removed construction-specific imports, and renamed the public API.
See LICENSES/Apache-2.0.txt at the repository root.
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Forced differential equations with a quadratic-form growth bound

These estimates hold in any real inner product space; completeness and
finite dimensionality are not needed. They are consequences of the actual
differential equation, not assumptions on an abstract propagator.

The right-derivative comparison treats zeroes of the solution explicitly.
A positive integrating factor removes variable growth, while an additional
constant growth rate costs an exponential. The interval-only forcing version
does not require a continuous extension to be supplied by the caller.

## References

* OpenAI, `NavierStokesAndEuler/NavierStokes/ViscousPropagator.lean`,
  revision `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`.
-/

namespace Mettapedia.Analysis.ODE

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Right derivative of the norm away from zero, obtained from the squared norm. -/
theorem hasDerivWithinAt_norm_of_ne_zero {u : ℝ → H} {u' : H} {s : Set ℝ} {t : ℝ}
    (hu : HasDerivWithinAt u u' s t) (hne : u t ≠ 0) :
    HasDerivWithinAt (fun x => ‖u x‖) (⟪u t, u'⟫_ℝ / ‖u t‖) s t := by
  have hn : ‖u t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hs := hu.norm_sq.sqrt (pow_ne_zero 2 hn)
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    using hs

/-- A dissipative linear equation grows in norm by at most its integrated forcing.
The equation is required only as a right derivative on the finite interval. -/
theorem norm_le_initial_add_integral_of_dissipative
    {a b : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (hu : ContinuousOn u (Icc a b)) (hf : Continuous f)
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H, ⟪x, A t x⟫_ℝ ≤ 0) :
    ∀ t ∈ Icc a b, ‖u t‖ ≤ ‖u a‖ + ∫ s in a..t, ‖f s‖ := by
  let B : ℝ → ℝ := fun t => ‖u a‖ + ∫ s in a..t, ‖f s‖
  have hB (t : ℝ) : HasDerivAt B ‖f t‖ t :=
    (intervalIntegral.integral_hasDerivAt_right (hf.norm.intervalIntegrable a t)
      (hf.norm.stronglyMeasurableAtFilter _ _) hf.norm.continuousAt).const_add ‖u a‖
  apply image_le_of_liminf_slope_right_le_deriv_boundary
    (continuous_norm.comp_continuousOn hu) (by simp [B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt)
  intro t ht r hr
  by_cases hz : u t = 0
  · have hd : HasDerivWithinAt u (f t) (Ici t) t := by
      simpa [hz] using hode t ht
    exact hd.liminf_right_slope_norm_le hr
  · have hn : 0 < ‖u t‖ := norm_pos_iff.mpr hz
    have hi : ⟪u t, A t (u t) + f t⟫_ℝ ≤ ‖u t‖ * ‖f t‖ := by
      rw [inner_add_right]
      exact (add_le_add (hA t ht (u t)) (real_inner_le_norm (u t) (f t))).trans_eq
        (zero_add _)
    have hdiv : ⟪u t, A t (u t) + f t⟫_ℝ / ‖u t‖ ≤ ‖f t‖ := by
      apply (div_le_iff₀ hn).2
      simpa only [mul_comm] using hi
    exact (hasDerivWithinAt_norm_of_ne_zero (hode t ht) hz).liminf_right_slope_le
      (lt_of_le_of_lt hdiv hr)

/-- Integrating-factor estimate from a quadratic-form bound on the actual operator.
`W` is a positive scalar solution of `W' = growth * W`; it is not a bound
assumed for the vector solution. -/
theorem norm_div_le_initial_add_integral
    {a b : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (growth W : ℝ → ℝ) (hWpos : ∀ t, 0 < W t)
    (hW : ∀ t, HasDerivAt W (growth t * W t) t)
    (hu : ContinuousOn u (Icc a b)) (hf : Continuous f)
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H,
      ⟪x, A t x⟫_ℝ ≤ growth t * ‖x‖ ^ 2) :
    ∀ t ∈ Icc a b,
      ‖u t‖ / W t ≤ ‖u a‖ / W a + ∫ s in a..t, ‖f s‖ / W s := by
  have hInv (t : ℝ) : HasDerivAt (fun s => (W s)⁻¹)
      (-growth t * (W t)⁻¹) t := by
    convert! (hW t).inv (ne_of_gt (hWpos t)) using 1
    field_simp [ne_of_gt (hWpos t)]
  have hcInv : Continuous (fun t => (W t)⁻¹) :=
    continuous_iff_continuousAt.mpr fun t => (hInv t).continuousAt
  let v : ℝ → H := fun t => (W t)⁻¹ • u t
  let F : ℝ → H := fun t => (W t)⁻¹ • f t
  let B : ℝ → H →L[ℝ] H := fun t => A t - growth t • ContinuousLinearMap.id ℝ H
  have hv : ContinuousOn v (Icc a b) := hcInv.continuousOn.smul hu
  have hF : Continuous F := hcInv.smul hf
  have hvode (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt v (B t (v t) + F t) (Ici t) t := by
    convert! (hInv t).hasDerivWithinAt.smul (hode t ht) using 1
    dsimp [v, F, B]
    simp only [sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_add]
    module
  have hB (t : ℝ) (ht : t ∈ Ico a b) (x : H) : ⟪x, B t x⟫_ℝ ≤ 0 := by
    dsimp [B]
    simp only [sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq]
    linarith [hA t ht x]
  have hn (t : ℝ) (x : H) : ‖(W t)⁻¹ • x‖ = ‖x‖ / W t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hWpos t)),
      div_eq_mul_inv, mul_comm]
  have h := norm_le_initial_add_integral_of_dissipative B hv hF hvode hB
  dsimp [v, F] at h
  simpa only [hn] using h

/-- A positive weight absorbs the variable reference
growth, while the remaining nonnegative error contributes one exponential. -/
theorem norm_le_exp_mul_weight_mul_integral
    {a b : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (rate P : ℝ → ℝ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hPpos : ∀ t, 0 < P t) (hP : ∀ t, HasDerivAt P (rate t * P t) t)
    (hu : ContinuousOn u (Icc a b)) (hf : Continuous f)
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H,
      ⟪x, A t x⟫_ℝ ≤ (rate t + μ) * ‖x‖ ^ 2) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ≤ Real.exp (μ * (t - a)) * P t *
        (‖u a‖ / P a + ∫ s in a..t, ‖f s‖ / P s) := by
  let W : ℝ → ℝ := fun t => P t * Real.exp (μ * (t - a))
  have hWpos (t : ℝ) : 0 < W t := mul_pos (hPpos t) (Real.exp_pos _)
  have hExp (t : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (μ * (s - a)))
      (μ * Real.exp (μ * (t - a))) t := by
    convert! (((hasDerivAt_id t).sub_const a).const_mul μ).exp using 1
    simp only [id, mul_one]
    ring
  have hW (t : ℝ) : HasDerivAt W ((rate t + μ) * W t) t := by
    convert! (hP t).mul (hExp t) using 1
    dsimp [W]
    ring
  have hcP : Continuous P := continuous_iff_continuousAt.mpr fun t => (hP t).continuousAt
  have hcW : Continuous W := continuous_iff_continuousAt.mpr fun t => (hW t).continuousAt
  have hF := hf.norm.div hcP (fun t => ne_of_gt (hPpos t))
  have hFW := hf.norm.div hcW (fun t => ne_of_gt (hWpos t))
  have hbase := norm_div_le_initial_add_integral A (fun t => rate t + μ) W
    hWpos hW hu hf hode hA
  intro t ht
  have hint : (∫ s in a..t, ‖f s‖ / W s) ≤ ∫ s in a..t, ‖f s‖ / P s := by
    apply intervalIntegral.integral_mono_on ht.1
      (hFW.intervalIntegrable a t) (hF.intervalIntegrable a t)
    intro s hs
    have he : 1 ≤ Real.exp (μ * (s - a)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hμ (sub_nonneg.mpr hs.1))
    have hPW : P s ≤ W s := by
      dsimp [W]
      nlinarith [hPpos s]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (hPpos s) hPW
  have hWa : W a = P a := by simp [W]
  have h := hbase t ht
  rw [hWa] at h
  have hout : ‖u t‖ / W t ≤ ‖u a‖ / P a + ∫ s in a..t, ‖f s‖ / P s :=
    h.trans (add_le_add_right hint _)
  calc
    ‖u t‖ ≤ (‖u a‖ / P a + ∫ s in a..t, ‖f s‖ / P s) * W t :=
      (div_le_iff₀ (hWpos t)).mp hout
    _ = Real.exp (μ * (t - a)) * P t *
        (‖u a‖ / P a + ∫ s in a..t, ‖f s‖ / P s) := by
      dsimp [W]
      ring

/-- Interval-only forcing version. Clamping the source outside the interval
shows that no global extension hypothesis on the forcing is needed. -/
theorem norm_le_exp_mul_weight_mul_integral_on
    {a b : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (rate P : ℝ → ℝ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hPpos : ∀ t, 0 < P t) (hP : ∀ t, HasDerivAt P (rate t * P t) t)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H,
      ⟪x, A t x⟫_ℝ ≤ (rate t + μ) * ‖x‖ ^ 2) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ≤ Real.exp (μ * (t - a)) * P t *
        (‖u a‖ / P a + ∫ s in a..t, ‖f s‖ / P s) := by
  by_cases hab : a ≤ b
  · let F : ℝ → H := fun s => f (projIcc a b hab s)
    have hF : Continuous F := hf.restrict.comp continuous_projIcc
    have hFeq (s : ℝ) (hs : s ∈ Icc a b) : F s = f s := by
      simp only [F, projIcc_of_mem hab hs]
    have hodeF (s : ℝ) (hs : s ∈ Ico a b) :
        HasDerivWithinAt u (A s (u s) + F s) (Ici s) s := by
      rw [hFeq s (Ico_subset_Icc_self hs)]
      exact hode s hs
    have h := norm_le_exp_mul_weight_mul_integral A rate P hμ hPpos hP hu hF hodeF hA
    intro t ht
    have heq : (∫ s in a..t, ‖F s‖ / P s) = ∫ s in a..t, ‖f s‖ / P s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      change ‖F s‖ / P s = ‖f s‖ / P s
      rw [hFeq s ⟨hs.1, hs.2.trans ht.2⟩]
    simpa only [heq] using h t ht
  · intro t ht
    exact False.elim (hab (ht.1.trans ht.2))

/-- A source bounded by `K * P` retains that envelope and costs at most the
interval length. No sign hypothesis on `K` is needed beyond the source inequality. -/
theorem norm_le_exp_mul_weight_mul_of_source_le
    {a b K : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (rate P : ℝ → ℝ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hPpos : ∀ t, 0 < P t) (hP : ∀ t, HasDerivAt P (rate t * P t) t)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H,
      ⟪x, A t x⟫_ℝ ≤ (rate t + μ) * ‖x‖ ^ 2)
    (hinit : u a = 0) (hsource : ∀ t ∈ Icc a b, ‖f t‖ ≤ K * P t) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ≤ Real.exp (μ * (t - a)) * P t * (K * (t - a)) := by
  have hcP : Continuous P := continuous_iff_continuousAt.mpr fun t => (hP t).continuousAt
  have hq : ContinuousOn (fun s => ‖f s‖ / P s) (Icc a b) :=
    hf.norm.div hcP.continuousOn (fun s _ => ne_of_gt (hPpos s))
  have h := norm_le_exp_mul_weight_mul_integral_on A rate P hμ hPpos hP hu hf hode hA
  intro t ht
  have hint : (∫ s in a..t, ‖f s‖ / P s) ≤ K * (t - a) := by
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
    have hi := intervalIntegral.integral_mono_on (μ := volume) ht.1
      ((hq.mono hsub).intervalIntegrable_of_Icc ht.1)
      (continuous_const.intervalIntegrable a t) (fun s hs =>
        (div_le_iff₀ (hPpos s)).mpr (hsource s (hsub hs)))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hi
  have hh := h t ht
  simp only [hinit, norm_zero, zero_div, zero_add] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hint
    (mul_nonneg (Real.exp_pos _).le (hPpos t).le))

end Mettapedia.Analysis.ODE
