import MettapediaNS.GaussianHeatCovariance
import NavierStokes.R3.HeatKernelFourier
import Mettapedia.Analysis.UnitTorusPeriodization

/-!
# Fourier normalization of the upstream Gaussian average

OpenAI's Gaussian Fourier theorem identifies the multiplier of its actual
whole-space averaging kernel. This adapter only reconciles the two upstream
heat-parameter conventions; it does not reprove the Gaussian transform.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianHeatCovariance

open MeasureTheory EulerWholeSpaceGaussian
open EulerSmoothLimit (Space)
open scoped FourierTransform
open scoped InnerProductSpace

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem kernel_eq_heatKernel (τ : ℝ) (x : Space) :
    kernel τ x = NavierStokesR3.Comparison.heatKernel (τ / 4) x := by
  unfold kernel normalization NavierStokesR3.Comparison.heatKernel
  congr 2 <;> ring

/-- The literal upstream displacement kernel has the expected Gaussian
Fourier multiplier. The integral transform is imported, not reconstructed. -/
theorem fourier_kernel {τ : ℝ} (hτ : 0 < τ) (ξ : Space) :
    𝓕 (fun y : Space => (kernel τ y : ℂ)) ξ =
      (Real.exp (-(Real.pi ^ 2 * τ) * ‖ξ‖ ^ 2) : ℂ) := by
  have hk : (fun y : Space => (kernel τ y : ℂ)) =
      (normalization τ : ℂ) • (fun y : Space => (Real.exp (-τ⁻¹ * ‖y‖ ^ 2) : ℂ)) := by
    ext y
    simp only [kernel, Complex.ofReal_mul, Pi.smul_apply, smul_eq_mul]
  rw [hk]
  change VectorFourier.fourierIntegral _ _ _ (_ • _) ξ = _
  rw [VectorFourier.fourierIntegral_const_smul]
  change (normalization τ : ℂ) *
    (𝓕 (fun y : Space => (Real.exp (-τ⁻¹ * ‖y‖ ^ 2) : ℂ))) ξ = _
  rw [NavierStokesR3.Comparison.fourierIntegral_gaussian_real (inv_pos.mpr hτ)]
  have hn : normalization τ * (Real.pi * τ) ^ (3 / 2 : ℝ) = 1 := by
    rw [normalization, ← Real.rpow_add (mul_pos Real.pi_pos hτ)]
    norm_num
  simp only [← Complex.ofReal_mul, div_inv_eq_mul]
  rw [← mul_assoc, hn, one_mul]
  congr 2
  ring

/-- Plane waves need not belong to whole-space `L²`: the literal Gaussian
average nevertheless acts on them by this exact multiplier. -/
theorem average_fourierChar {τ : ℝ} (hτ : 0 < τ) (ξ x : Space) :
    average τ (fun y : Space => (Real.fourierChar (-⟪y, ξ⟫_ℝ) : ℂ)) x =
      (Real.fourierChar (-⟪x, ξ⟫_ℝ) : ℂ) *
        (Real.exp (-(Real.pi ^ 2 * τ) * ‖ξ‖ ^ 2) : ℂ) := by
  rw [← fourier_kernel hτ ξ, Real.fourier_eq, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    simp only [inner_add_left, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul,
      Circle.smul_def, smul_eq_mul, Complex.real_smul]
    ring)

/-- The existing periodization construction gives the exact unit-torus heat
symbol at every lattice frequency, without a finite-mode truncation. -/
theorem mFourierCoeff_periodized_kernel {τ : ℝ} (hτ : 0 < τ) (n : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff
      (Mettapedia.Analysis.UnitTorusPeriodization.periodize
        (fun y : Space => (kernel τ y : ℂ))) n =
      (Real.exp (-(Real.pi ^ 2 * τ) *
        ‖Mettapedia.Analysis.UnitTorusLattice.frequency n‖ ^ 2) : ℂ) := by
  have hm : Measurable (fun y : Space => (kernel τ y : ℂ)) :=
    (Complex.continuous_ofReal.comp (kernel_smooth τ).continuous).measurable
  have hi : Integrable (fun y : Space => (kernel τ y : ℂ)) := (kernel_integrable hτ).ofReal
  rw [Mettapedia.Analysis.UnitTorusPeriodization.mFourierCoeff_periodize _ hm hi]
  exact fourier_kernel hτ _

end Mettapedia.FluidDynamics.NavierStokes.GaussianHeatCovariance
