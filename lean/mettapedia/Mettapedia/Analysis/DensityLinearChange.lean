import Mettapedia.Analysis.SchwartzLinearChange

/-! Linear changes of nonnegative integrable densities and their spatial moments. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.DensityLinearChange

open MeasureTheory SchwartzLinearChange

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def pullbackDensity (L : E ≃L[ℝ] E) (H : E → ℝ) (x : E) : ℝ := jacobian L * H (L x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem pullbackDensity_nonneg (L : E ≃L[ℝ] E) (H : E → ℝ) (hH : ∀ x, 0 ≤ H x) (x : E) :
    0 ≤ pullbackDensity L H x := mul_nonneg (jacobian_pos L).le (hH _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_pullbackDensity (L : E ≃L[ℝ] E) (H : E → ℝ) (hH : Continuous H) :
    Continuous (pullbackDensity L H) := continuous_const.mul (hH.comp L.continuous)

theorem integrable_pullbackDensity (L : E ≃L[ℝ] E) (H : E → ℝ) (hH : Integrable H) :
    Integrable (pullbackDensity L H) := by
  have hm : Measure.map L (volume : Measure E) =
      ENNReal.ofReal |(LinearMap.det L.toLinearMap)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  have hi : Integrable H (Measure.map L volume) := by
    rw [hm]
    exact hH.smul_measure ENNReal.ofReal_ne_top
  exact ((integrable_map_equiv L.toHomeomorph.toMeasurableEquiv H).mp hi).const_mul _

theorem integral_pullbackDensity (L : E ≃L[ℝ] E) (H : E → ℝ) :
    (∫ x : E, pullbackDensity L H x) = ∫ x : E, H x :=
  integral_jacobian_comp L H

/-- Change of variables with an arbitrary scalar observable retained. -/
theorem integral_mul_pullbackDensity (L : E ≃L[ℝ] E) (H w : E → ℝ) :
    (∫ x : E, w x * pullbackDensity L H x) = ∫ y : E, w (L.symm y) * H y := by
  have he (x : E) : w x * pullbackDensity L H x =
      pullbackDensity L (fun y ↦ w (L.symm y) * H y) x := by
    simp only [pullbackDensity, L.symm_apply_apply]
    ring
  simp_rw [he]
  exact integral_pullbackDensity _ _

theorem integrable_mul_pullbackDensity (L : E ≃L[ℝ] E) (H w : E → ℝ)
    (hi : Integrable (fun y ↦ w (L.symm y) * H y)) :
    Integrable (fun x : E ↦ w x * pullbackDensity L H x) := by
  have he (x : E) : w x * pullbackDensity L H x =
      pullbackDensity L (fun y ↦ w (L.symm y) * H y) x := by
    simp only [pullbackDensity, L.symm_apply_apply]
    ring
  simp_rw [he]
  exact integrable_pullbackDensity _ _ hi

theorem integral_moment_pullbackDensity (L : E ≃L[ℝ] E) (H : E → ℝ) (m : ℕ) :
    (∫ x : E, ‖x‖ ^ m * pullbackDensity L H x) =
      ∫ y : E, ‖L.symm y‖ ^ m * H y :=
  integral_mul_pullbackDensity L H (fun x ↦ ‖x‖ ^ m)

theorem integrable_moment_pullbackDensity (L : E ≃L[ℝ] E) (H : E → ℝ)
    (hH : ∀ x, 0 ≤ H x) (hHc : Continuous H) (m : ℕ)
    (hHm : Integrable (fun x ↦ ‖x‖ ^ m * H x)) :
    Integrable (fun x ↦ ‖x‖ ^ m * pullbackDensity L H x) := by
  have hi : Integrable (fun y ↦ ‖L.symm y‖ ^ m * H y) := by
    apply (hHm.const_mul (‖L.symm.toContinuousLinearMap‖ ^ m)).mono'
      (((L.symm.continuous.norm).pow m).mul hHc).aestronglyMeasurable
    filter_upwards [] with y
    change ‖‖L.symm y‖ ^ m * H y‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (hH y))]
    calc
      _ ≤ (‖L.symm.toContinuousLinearMap‖ * ‖y‖) ^ m * H y := by
        apply mul_le_mul_of_nonneg_right _ (hH y)
        gcongr
        exact L.symm.toContinuousLinearMap.le_opNorm y
      _ = _ := by rw [mul_pow]; ring
  exact integrable_mul_pullbackDensity L H (fun x ↦ ‖x‖ ^ m) hi

theorem integral_moment_pullbackDensity_le (L : E ≃L[ℝ] E) (H : E → ℝ)
    (hH : ∀ x, 0 ≤ H x) (m : ℕ) (hHm : Integrable (fun x ↦ ‖x‖ ^ m * H x)) :
    (∫ x : E, ‖x‖ ^ m * pullbackDensity L H x) ≤
      ‖L.symm.toContinuousLinearMap‖ ^ m * ∫ x : E, ‖x‖ ^ m * H x := by
  rw [integral_moment_pullbackDensity, ← integral_const_mul]
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun y ↦ mul_nonneg (pow_nonneg (norm_nonneg _) _) (hH y)))
    (hHm.const_mul _)
  filter_upwards [] with y
  calc
    _ ≤ (‖L.symm.toContinuousLinearMap‖ * ‖y‖) ^ m * H y := by
      apply mul_le_mul_of_nonneg_right _ (hH y)
      gcongr
      exact L.symm.toContinuousLinearMap.le_opNorm y
    _ = _ := by rw [mul_pow]; ring

end Mettapedia.Analysis.DensityLinearChange
