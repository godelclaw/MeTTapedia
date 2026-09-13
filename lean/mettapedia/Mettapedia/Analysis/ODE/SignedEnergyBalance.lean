import Mettapedia.Analysis.ODE.VariableGronwall

/-!
# Integrating factors for signed energy balances

A constant growth coefficient is removed without taking the absolute value
of the residual. Energy, dissipation, residual and coefficient may have
either sign. Derivatives are required only in the interval interior.
-/

namespace Mettapedia.Analysis.ODE

open Set

theorem exp_mul_add_integral_le_of_deriv_le
    {t : ℝ} (ht : 0 ≤ t) (c : ℝ) {F F' D W : ℝ → ℝ}
    (hF : ContinuousOn F (Icc 0 t)) (hD : ContinuousOn D (Icc 0 t))
    (hW : ContinuousOn W (Icc 0 t))
    (hder : ∀ τ ∈ Ioo 0 t, HasDerivAt F (F' τ) τ)
    (hbound : ∀ τ ∈ Ioo 0 t, F' τ + D τ ≤ c * F τ + W τ) :
    Real.exp (-c * t) * F t + (∫ τ in (0 : ℝ)..t, Real.exp (-c * τ) * D τ) ≤
      F 0 + ∫ τ in (0 : ℝ)..t, Real.exp (-c * τ) * W τ := by
  have hw : Continuous (fun τ : ℝ ↦ Real.exp (-c * τ)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hdw (τ : ℝ) : HasDerivAt (fun r : ℝ ↦ Real.exp (-c * r))
      (-c * Real.exp (-c * τ)) τ := by
    simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id τ).const_mul (-c)).exp
  have hprod (τ : ℝ) (hτ : τ ∈ Ioo 0 t) :
      HasDerivAt (fun r ↦ Real.exp (-c * r) * F r)
        (Real.exp (-c * τ) * (F' τ - c * F τ)) τ := by
    convert! (hdw τ).mul (hder τ hτ) using 1
    ring
  have he := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le ht
    (hw.continuousOn.mul hF) (fun τ hτ ↦ (hprod τ hτ).hasDerivWithinAt)
    (((hw.continuousOn.mul hW).sub (hw.continuousOn.mul hD)).integrableOn_Icc)
    (fun τ hτ ↦ ?_)
  · rw [intervalIntegral.integral_sub
      ((hw.continuousOn.mul hW).intervalIntegrable_of_Icc ht)
      ((hw.continuousOn.mul hD).intervalIntegrable_of_Icc ht)] at he
    simp only [Pi.mul_apply, mul_zero, Real.exp_zero, one_mul] at he
    linarith only [he]
  · have h := mul_le_mul_of_nonneg_left (hbound τ hτ) (Real.exp_pos (-c * τ)).le
    change Real.exp (-c * τ) * (F' τ - c * F τ) ≤
      Real.exp (-c * τ) * W τ - Real.exp (-c * τ) * D τ
    nlinarith only [h]

end Mettapedia.Analysis.ODE
