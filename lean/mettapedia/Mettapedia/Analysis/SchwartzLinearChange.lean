import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Linear changes of Schwartz kernels

Multiplying a pullback by its absolute Jacobian preserves kernel mass.
Spatial moments transform by the inverse linear map, and the Fourier
symbol transforms by its adjoint. These identities retain the exact
coordinate cost rather than absorbing it in an unspecified constant.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SchwartzLinearChange

open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def jacobian (L : E ≃L[ℝ] E) : ℝ := |LinearMap.det L.toLinearMap|

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem jacobian_pos (L : E ≃L[ℝ] E) : 0 < jacobian L :=
  abs_pos.mpr (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero

theorem integral_comp_linearEquiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E ≃L[ℝ] E) (f : E → F) :
    (∫ x : E, f (L x)) = (jacobian L)⁻¹ • ∫ x : E, f x := by
  have he := integral_map_equiv (μ := (volume : Measure E)) L.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map L (volume : Measure E) =
      ENNReal.ofReal |(LinearMap.det L.toLinearMap)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  change (∫ y : E, f y ∂Measure.map L volume) = ∫ x : E, f (L x) at he
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv] at he
  exact he.symm

/-- Density pullback: its absolute Jacobian exactly compensates the change of variables. -/
def pullback (L : E ≃L[ℝ] E) (s : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  jacobian L • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L s

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem pullback_apply (L : E ≃L[ℝ] E) (s : 𝓢(E, ℂ)) (x : E) :
    pullback L s x = jacobian L • s (L x) := rfl

theorem integral_jacobian_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E ≃L[ℝ] E) (f : E → F) :
    (∫ x : E, jacobian L • f (L x)) = ∫ x : E, f x := by
  rw [integral_smul, integral_comp_linearEquiv, smul_smul,
    mul_inv_cancel₀ (jacobian_pos L).ne', one_smul]

theorem fourier_pullback (L : E ≃L[ℝ] E) (s : 𝓢(E, ℂ)) (ξ : E) :
    (𝓕 (pullback L s)) ξ = (𝓕 s) (L.symm.toContinuousLinearMap.adjoint ξ) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq, SchwartzMap.fourier_coe, Real.fourier_eq]
  have hi (x : E) : ⟪L x, L.symm.toContinuousLinearMap.adjoint ξ⟫ = ⟪x, ξ⟫ := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp
  have he (x : E) :
      Real.fourierChar (-⟪x, ξ⟫) • pullback L s x =
        jacobian L • (Real.fourierChar (-⟪L x, L.symm.toContinuousLinearMap.adjoint ξ⟫) • s (L x)) := by
    rw [hi, pullback_apply, smul_comm]
  simp_rw [he]
  exact integral_jacobian_comp L
    (fun y : E ↦ Real.fourierChar (-⟪y, L.symm.toContinuousLinearMap.adjoint ξ⟫) • s y)

theorem moment_pullback (L : E ≃L[ℝ] E) (s : 𝓢(E, ℂ)) (m : ℕ) :
    (∫ x : E, ‖x‖ ^ m * ‖pullback L s x‖) =
      ∫ y : E, ‖L.symm y‖ ^ m * ‖s y‖ := by
  have he (x : E) : ‖x‖ ^ m * ‖pullback L s x‖ =
      jacobian L • (‖L.symm (L x)‖ ^ m * ‖s (L x)‖) := by
    simp only [pullback_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (jacobian_pos L), L.symm_apply_apply, smul_eq_mul]
    ring
  simp_rw [he]
  exact integral_jacobian_comp L (fun y : E ↦ ‖L.symm y‖ ^ m * ‖s y‖)

theorem mass_pullback (L : E ≃L[ℝ] E) (s : 𝓢(E, ℂ)) :
    (∫ x : E, ‖pullback L s x‖) = ∫ y : E, ‖s y‖ := by
  simpa using moment_pullback L s 0

theorem moment_pullback_le (L : E ≃L[ℝ] E) (s : 𝓢(E, ℂ)) (m : ℕ) :
    (∫ x : E, ‖x‖ ^ m * ‖pullback L s x‖) ≤
      ‖L.symm.toContinuousLinearMap‖ ^ m * ∫ y : E, ‖y‖ ^ m * ‖s y‖ := by
  rw [moment_pullback, ← integral_const_mul]
  have hright : Integrable (fun y : E ↦
      ‖L.symm.toContinuousLinearMap‖ ^ m * (‖y‖ ^ m * ‖s y‖)) :=
    (s.integrable_pow_mul (volume : Measure E) m).const_mul _
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ ↦ by positivity)) hright
  filter_upwards [] with y
  calc
    ‖L.symm y‖ ^ m * ‖s y‖ ≤ (‖L.symm.toContinuousLinearMap‖ * ‖y‖) ^ m * ‖s y‖ := by
      gcongr
      exact L.symm.toContinuousLinearMap.le_opNorm y
    _ = _ := by rw [mul_pow]; ring

end Mettapedia.Analysis.SchwartzLinearChange
