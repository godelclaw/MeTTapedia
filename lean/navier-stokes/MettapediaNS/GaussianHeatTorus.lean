import MettapediaNS.GaussianHeatFourier
import MettapediaNS.GaussianHeatEnergy
import Mettapedia.Analysis.UnitTorusIntegrableConvolution

/-!
# The actual Gaussian average on periodic fields

The literal upstream whole-space average of a periodic lift equals
convolution by the existing periodized kernel. The existing integrable
convolution theorem then gives its Fourier series. Periodic lifts are
not assumed to be whole-space L² functions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianHeatCovariance

open MeasureTheory EulerWholeSpaceGaussian
open EulerSmoothLimit (Space)
open Mettapedia.Analysis UnitTorusPeriodization UnitTorusLattice
open scoped FourierTransform Convolution

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The existing lattice periodization, with the actual upstream Gaussian. -/
def periodicKernel (τ : ℝ) : T3 → ℂ :=
  periodize (fun y : Space => (kernel τ y : ℂ))

theorem periodicKernel_integrable {τ : ℝ} (hτ : 0 < τ) : Integrable (periodicKernel τ) :=
  integrable_periodize_of_integrable _
    (Complex.continuous_ofReal.comp (kernel_smooth τ).continuous).measurable
    (kernel_integrable hτ).ofReal

theorem mFourierCoeff_periodicKernel {τ : ℝ} (hτ : 0 < τ) (n : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (periodicKernel τ) n =
      (Real.exp (-(Real.pi ^ 2 * τ) * ‖frequency n‖ ^ 2) : ℂ) :=
  mFourierCoeff_periodized_kernel hτ n

/-- Actual periodic convolution, before imposing regularity on the input. -/
def periodicAverage (τ : ℝ) (f : T3 → ℂ) (x : T3) : ℂ :=
  ∫ h : T3, periodicKernel τ h * f (x - h)

/-- Equality with OpenAI's literal Gaussian averaging of a periodic lift. -/
theorem average_lift_eq_periodicAverage {τ : ℝ} (hτ : 0 < τ)
    (f : C(T3, ℂ)) (x : Space) :
    average τ (fun y : Space => f (torusProjection y)) x =
      periodicAverage τ f (torusProjection x) := by
  have hm : Measurable (fun y : Space => (kernel τ y : ℂ)) :=
    (Complex.continuous_ofReal.comp (kernel_smooth τ).continuous).measurable
  have hi : Integrable (fun y : Space => (kernel τ y : ℂ)) := (kernel_integrable hτ).ofReal
  have hs : Continuous (fun h : T3 => torusProjection x - h) :=
    continuous_sub_left (torusProjection x)
  let g : C(T3, ℂ) := ⟨fun h => f (torusProjection x - h), f.continuous.comp hs⟩
  have hp (y : Space) : torusProjection (x - y) = torusProjection x - torusProjection y := by
    ext i
    simp [torusProjection]
  have hr := integral_smul_periodize _ hm hi g
  calc
    _ = ∫ y : Space, (kernel τ y : ℂ) * f (torusProjection (x - y)) := by
      rw [average_eq_convolution, convolution_lsmul]
      simp only [Complex.real_smul]
    _ = ∫ y : Space, g (torusProjection y) • (kernel τ y : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with y
      change (kernel τ y : ℂ) * f (torusProjection (x - y)) =
        f (torusProjection x - torusProjection y) * (kernel τ y : ℂ)
      rw [hp, mul_comm]
    _ = ∫ q : T3, g q • periodicKernel τ q := hr.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with q
      exact mul_comm _ _

theorem continuous_periodicAverage {τ : ℝ} (hτ : 0 < τ) (f : C(T3, ℂ)) :
    Continuous (periodicAverage τ f) := by
  change Continuous ((periodicKernel τ) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f)
  exact (HasCompactSupport.of_compactSpace f).continuous_convolution_right _
    (periodicKernel_integrable hτ).locallyIntegrable f.continuous

/-- The infinite series is transported by the existing integrable-kernel
pairing, not by a new termwise-integration argument. -/
theorem hasSum_periodicAverage {τ : ℝ} (hτ : 0 < τ) (f : C(T3, ℂ))
    (a : (Fin 3 → ℤ) → ℂ)
    (ha : HasSum (fun n => a n • UnitAddTorus.mFourier n) f) (x : T3) :
    HasSum (fun n => (Real.exp (-(Real.pi ^ 2 * τ) * ‖frequency n‖ ^ 2) : ℂ) *
      UnitAddTorus.mFourier n x * a n) (periodicAverage τ f x) := by
  simpa only [mFourierCoeff_periodicKernel hτ, periodicAverage] using
    UnitTorusIntegrableConvolution.hasSum_convolution (periodicKernel τ)
      (periodicKernel_integrable hτ) f a ha x

/-- Fourier reconstruction is supplied by mathlib, rather than a separate
series assumption, when the actual coefficients are summable. -/
theorem average_lift_eq_tsum {τ : ℝ} (hτ : 0 < τ) (f : C(T3, ℂ))
    (hf : Summable (UnitAddTorus.mFourierCoeff f)) (x : Space) :
    average τ (fun y : Space => f (torusProjection y)) x =
      ∑' n : Fin 3 → ℤ, (Real.exp (-(Real.pi ^ 2 * τ) * ‖frequency n‖ ^ 2) : ℂ) *
        UnitAddTorus.mFourier n (torusProjection x) * UnitAddTorus.mFourierCoeff f n := by
  rw [average_lift_eq_periodicAverage hτ]
  exact (hasSum_periodicAverage hτ f (UnitAddTorus.mFourierCoeff f)
    (UnitAddTorus.hasSum_mFourier_series_of_summable hf) (torusProjection x)).tsum_eq.symm

end Mettapedia.FluidDynamics.NavierStokes.GaussianHeatCovariance
