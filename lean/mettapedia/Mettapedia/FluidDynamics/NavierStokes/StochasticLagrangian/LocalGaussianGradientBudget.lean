import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalGaussianPressurePartition

/-!
# An integrable spatial gradient budget for the constructed Gaussian patches

This closes the spatial construction with actual vorticity and strain
gradients. It does not assert that the budget is uniform in the spectral
threshold, the localization radius, time, or dyadic scale. Passing this
bound to finite Fourier approximants remains a separate approximation step.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalGaussianGradientBudget

open scoped BigOperators
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFilteredStrainDynamics PancakeFourierStrainGradient PancakeHigherDerivativeMoments
open PancakeFourierTranslationCurve LocalLowDiffusionBudget LocalSpatialVorticityJets
open LocalSquaredGapPressure LocalGaussianPressurePartition AdaptiveGaussianLinePartition SpectralTiltFreezing

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def gradientDensity (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (rho tau : ℝ) (x : T3) : ℝ :=
  3 * (1 + localWeight gamma chi modes u x * rho ^ 2 / (2 * tau ^ 2)) *
    ((2 / gamma ^ 2) * (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) +
      (800 * ‖fullVorticity u x‖ ^ 2 / gamma ^ 4) *
        (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2))

theorem continuous_gradientDensity (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (rho tau : ℝ) :
    Continuous (gradientDensity gamma chi modes u rho tau) := by
  have hw := continuous_fullVorticity u hu
  have ha : Continuous (localWeight gamma chi modes u) :=
    SquaredGapTiltWeight.continuous_weight gamma hg _ _
      (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u)) hw
  have hv : Continuous (fun x : T3 ↦ ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ ↦ (LocalSquaredGapGradient.continuous_fullCurlGradient u j).norm.pow 2)
  have hS : Continuous (fun x : T3 ↦ ∑ j : Fin 3,
      ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ ↦ (LocalStrainGradientDensity.continuous_strainGradient chi modes u j).norm.pow 2)
  exact (continuous_const.mul (continuous_const.add ((ha.mul continuous_const).div_const _))).mul
    ((continuous_const.mul hv).add (((continuous_const.mul (hw.norm.pow 2)).div_const _).mul hS))

theorem exists_local_gaussian_gradient_budget (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (rho : ℝ) (hrho : 0 < rho) :
    ∃ centers : Finset T3, centers.Nonempty ∧
      let tau := temperature centers.card rho
      let p := patch gamma chi modes u centers tau
      0 < tau ∧ (∀ i, Continuous (p i)) ∧
      (∀ x, (∑ i, p i x ^ 2) = localWeight gamma chi modes u x) ∧
      (∀ x, (∑ i, p i x ^ 2 *
        lineDistanceSq (localDirection chi modes u x) (localDirection chi modes u i.1)) ≤ rho ^ 2) ∧
      (∀ i j, ∀ᵐ x : T3, DifferentiableAt ℝ (fun h : ℝ ↦ p i (x + coordinateShift j h)) 0) ∧
      (∀ᵐ x : T3, patchGradientSquare gamma chi modes u centers tau x ≤
        gradientDensity gamma chi modes u rho tau x) ∧
      Integrable (patchGradientSquare gamma chi modes u centers tau) ∧
      (∫ x : T3, patchGradientSquare gamma chi modes u centers tau x) ≤
        ∫ x : T3, gradientDensity gamma chi modes u rho tau x := by
  obtain ⟨centers, hc, ht, hp, hmass, hline, hd, hbudget⟩ :=
    exists_local_gaussian_partition gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) rho hrho
  let tau := temperature centers.card rho
  have hbound : ∀ᵐ x : T3, patchGradientSquare gamma chi modes u centers tau x ≤
      gradientDensity gamma chi modes u rho tau x := by
    filter_upwards [hbudget] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_left
      (LocalSquaredGapGradient.gradientSquare_le gamma hg chi modes u hu x)
      (show 0 ≤ 3 * (1 + localWeight gamma chi modes u x * rho ^ 2 / (2 * tau ^ 2)) by
        unfold localWeight SquaredGapTiltWeight.weight
        positivity))
  have hD : Integrable (gradientDensity gamma chi modes u rho tau) :=
    (continuous_gradientDensity gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu) rho tau).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hG : Integrable (patchGradientSquare gamma chi modes u centers tau) := by
    apply hD.mono' (stronglyMeasurable_patchGradientSquare gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu) centers hc tau).aestronglyMeasurable
    filter_upwards [hbound] with x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ patchGradientSquare gamma chi modes u centers tau x from
      Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))]
  exact ⟨centers, hc, ht, hp, hmass, hline, hd, hbound, hG, integral_mono_ae hG hD hbound⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalGaussianGradientBudget
