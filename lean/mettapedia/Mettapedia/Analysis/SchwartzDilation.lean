import Mettapedia.Analysis.SchwartzLinearChange

/-! Exact isotropic dilation of Schwartz kernels, their symbols, and spatial moments. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SchwartzDilation

open MeasureTheory SchwartzLinearChange
open scoped FourierTransform SchwartzMap RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def dilationEquiv (r : ℝ) (hr : r ≠ 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)

@[simp] theorem dilationEquiv_apply (r : ℝ) (hr : r ≠ 0) (x : E) :
    dilationEquiv r hr x = r • x := rfl

@[simp] theorem dilationEquiv_symm_apply (r : ℝ) (hr : r ≠ 0) (x : E) :
    (dilationEquiv r hr).symm x = r⁻¹ • x := rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem jacobian_dilationEquiv (r : ℝ) (hr : r ≠ 0) :
    jacobian (dilationEquiv (E := E) r hr) = |r| ^ Module.finrank ℝ E := by
  have h : (dilationEquiv (E := E) r hr).toLinearMap = r • LinearMap.id := by ext x; rfl
  simp [jacobian, h, LinearMap.det_smul, abs_pow]

def dilate (r : ℝ) (hr : r ≠ 0) (s : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  pullback (dilationEquiv r hr) s

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem dilate_apply (r : ℝ) (hr : r ≠ 0) (s : 𝓢(E, ℂ)) (x : E) :
    dilate r hr s x = |r| ^ Module.finrank ℝ E • s (r • x) := by
  rw [dilate, pullback_apply, jacobian_dilationEquiv, dilationEquiv_apply]

omit [MeasurableSpace E] [BorelSpace E] in
theorem inverse_adjoint_dilationEquiv (r : ℝ) (hr : r ≠ 0) (ξ : E) :
    (dilationEquiv r hr).symm.toContinuousLinearMap.adjoint ξ = r⁻¹ • ξ := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪(dilationEquiv r hr).symm x, ξ⟫ = _
  simp [real_inner_smul_left, inner_smul_right]

theorem fourier_dilate (r : ℝ) (hr : r ≠ 0) (s : 𝓢(E, ℂ)) (ξ : E) :
    (𝓕 (dilate r hr s)) ξ = (𝓕 s) (r⁻¹ • ξ) := by
  rw [dilate, fourier_pullback, inverse_adjoint_dilationEquiv]

theorem moment_dilate (r : ℝ) (hr : r ≠ 0) (s : 𝓢(E, ℂ)) (m : ℕ) :
    (∫ x : E, ‖x‖ ^ m * ‖dilate r hr s x‖) =
      |r|⁻¹ ^ m * ∫ x : E, ‖x‖ ^ m * ‖s x‖ := by
  rw [dilate, moment_pullback]
  simp only [dilationEquiv_symm_apply, norm_smul, Real.norm_eq_abs, abs_inv, mul_pow]
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

theorem mass_dilate (r : ℝ) (hr : r ≠ 0) (s : 𝓢(E, ℂ)) :
    (∫ x : E, ‖dilate r hr s x‖) = ∫ x : E, ‖s x‖ := by
  simpa using moment_dilate r hr s 0

end Mettapedia.Analysis.SchwartzDilation
