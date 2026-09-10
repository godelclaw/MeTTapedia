import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSquaredGapPressure
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialSpectralRelation
import Mettapedia.Analysis.LocallyLipschitzDifferentiability

/-!
# The actual spatial derivative cost of the squared-gap projector

The weighted projector's coordinate derivatives are bounded by the full
vorticity gradient and the actual filtered strain gradient. No spectral
gap is assumed. At nondifferentiability points Lean's total derivative
is zero; almost-everywhere differentiability is proved separately from
local Lipschitz regularity. Thus the estimates concern actual derivatives
almost everywhere, not only the total derivative's zero default. These
bounds retain their inverse-threshold costs and are not uniform as the
gap cutoff tends to zero.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapGradient

open scoped BigOperators
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFilteredStrainDynamics PancakeFourierTranslationCurve PancakeFourierStrainGradient
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalSpatialSpectralRelation LocalSquaredGapPressure
open PancakeFourierMaterialPaths PancakeHigherDerivativeMoments PancakeHaarTransportRate
open PancakeInfiniteFourierDerivative PancakeGalerkinKineticEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : CompleteSpace R3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℝ)
local instance : CompleteSpace (R3 →L[ℝ] R3) := ContinuousLinearMap.instCompleteSpace

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def coordinateDerivative (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) : R3 →L[ℝ] R3 :=
  deriv (fun h : ℝ ↦ localProjector gamma chi modes u (x + coordinateShift j h)) 0

def gradientSquare (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, ‖coordinateDerivative gamma chi modes u j x‖ ^ 2

/-- The derivatives used below are actual coordinate derivatives almost
everywhere for normalized periodic Haar measure, even at gap transitions. -/
theorem ae_coordinate_differentiable (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (j : Fin 3) :
    ∀ᵐ x : T3, DifferentiableAt ℝ
      (fun h : ℝ ↦ localProjector gamma chi modes u (x + coordinateShift j h)) 0 := by
  have hf := continuous_localProjector gamma hg chi modes u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu)
  have hjoint : Continuous (fun z : T3 × ℝ ↦ localProjector gamma chi modes u (z.1 + coordinateShift j z.2)) :=
    hf.comp (continuous_fst.add ((continuous_coordinateShift j).comp continuous_snd))
  have hm := measurableSet_of_differentiableAt_with_param ℝ
    (f := fun x h ↦ localProjector gamma chi modes u (x + coordinateShift j h)) hjoint
  have hm0 := hm.preimage (show Measurable (fun x : T3 ↦ (x, (0 : ℝ))) from
    measurable_id.prodMk measurable_const)
  apply PancakeAEMaterialRate.ae_torus_of_ae_real _ hm0
  have hreal := (locallyLipschitz_localProjector gamma hg chi modes u hu).ae_differentiableAt
    (volume : Measure X3)
  filter_upwards [hreal] with r hr
  have hline : DifferentiableAt ℝ (fun h : ℝ ↦ r + h • Pi.single j 1) 0 := by fun_prop
  have hr' : DifferentiableAt ℝ (fun r : X3 ↦ localProjector gamma chi modes u (torusPoint r))
      (r + (0 : ℝ) • Pi.single j 1) := by simpa only [zero_smul, add_zero] using hr
  simpa only [Function.comp_def, LocalSpatialBottomProjector.torusPoint_add_single] using hr'.comp 0 hline

theorem norm_coordinateDerivative_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) (x : T3) :
    ‖coordinateDerivative gamma chi modes u j x‖ ≤ ‖fullCurlGradient u j x‖ / gamma +
      20 * ‖fullVorticity u x‖ * ‖strainGradient modes (filteredVelocity chi u) x j‖ / gamma ^ 2 := by
  by_cases hM : DifferentiableAt ℝ
      (fun h : ℝ ↦ localProjector gamma chi modes u (x + coordinateShift j h)) 0
  · have h := SquaredGapTiltWeight.norm_derivative_weightedProjector_le gamma hg
      (strainCurve chi modes u j x) (fun h ↦ fullVorticity u (x + coordinateShift j h)) 0 _ _ _
      (hasDerivAt_strainCurve chi modes u j x 0) (hasDerivAt_fullVorticity_shift u hu j x 0)
      hM.hasDerivAt
    simpa only [coordinateShift_zero, add_zero, coordinateDerivative] using h
  · rw [coordinateDerivative, deriv_zero_of_not_differentiableAt hM, norm_zero]
    positivity

theorem gradientSquare_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (x : T3) :
    gradientSquare gamma chi modes u x ≤
      (2 / gamma ^ 2) * (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) +
      (800 * ‖fullVorticity u x‖ ^ 2 / gamma ^ 4) *
        (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2) := by
  unfold gradientSquare
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_coordinateDerivative_le gamma hg chi modes u hu j x) 2
  have hs := sq_nonneg (‖fullCurlGradient u j x‖ / gamma -
    20 * ‖fullVorticity u x‖ * ‖strainGradient modes (filteredVelocity chi u) x j‖ / gamma ^ 2)
  calc
    _ ≤ 2 * (‖fullCurlGradient u j x‖ / gamma) ^ 2 +
        800 * (‖fullVorticity u x‖ * ‖strainGradient modes (filteredVelocity chi u) x j‖ / gamma ^ 2) ^ 2 := by
      simp only [div_eq_mul_inv] at h hs ⊢
      nlinarith only [h, hs]
    _ = _ := by ring

theorem stronglyMeasurable_coordinateDerivative (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (j : Fin 3) :
    StronglyMeasurable (coordinateDerivative gamma chi modes u j) := by
  have hf := continuous_localProjector gamma hg chi modes u hu
  have hjoint : Continuous (fun z : T3 × ℝ ↦ localProjector gamma chi modes u (z.1 + coordinateShift j z.2)) :=
    hf.comp (continuous_fst.add ((continuous_coordinateShift j).comp continuous_snd))
  exact Continuous.stronglyMeasurable_deriv_const
    (f := fun x h ↦ localProjector gamma chi modes u (x + coordinateShift j h)) hjoint 0

theorem continuous_fullCurlGradient (u : FourierVelocity) (j : Fin 3) :
    Continuous (fullCurlGradient u j) :=
  PancakeDyadicDirectionEvolution.complexRealPartEuclideanCLM.continuous.comp
    (fullFourierField id (PancakeInfiniteFourierDerivative.indexedDerivativeCoeff id j
      (fourierCurl u))).continuous

theorem integrable_gradientSquare (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) : Integrable (gradientSquare gamma chi modes u) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hD : Continuous (fun x : T3 ↦ (2 / gamma ^ 2) * (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) +
      (800 * ‖fullVorticity u x‖ ^ 2 / gamma ^ 4) *
        (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2)) := by
    exact (continuous_const.mul (continuous_finsetSum _ (fun j _ ↦
      (continuous_fullCurlGradient u j).norm.pow 2))).add
      (((continuous_const.mul (hw.norm.pow 2)).div_const _).mul
        (continuous_finsetSum _ (fun j _ ↦ (LocalStrainGradientDensity.continuous_strainGradient chi modes u j).norm.pow 2)))
  have hG : StronglyMeasurable (gradientSquare gamma chi modes u) := by
    exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun j _ ↦
      (stronglyMeasurable_coordinateDerivative gamma hg chi modes u
        (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu) j).norm.pow 2)
  apply (hD.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mono' hG.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))]
  exact gradientSquare_le gamma hg chi modes u hu x

theorem integral_gradientSquare_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T3, gradientSquare gamma chi modes u x) ≤
      (2 / gamma ^ 2) * (∫ x : T3, ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) +
      (800 / gamma ^ 4) * (∫ x : T3, ‖fullVorticity u x‖ ^ 2 *
        (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2)) := by
  have hi : Integrable (fun x : T3 ↦ ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) :=
    (continuous_finsetSum _ (fun j _ ↦ (continuous_fullCurlGradient u j).norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 2 *
      (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2)) :=
    (((continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)).norm.pow 2).mul
      (continuous_finsetSum _ (fun j _ ↦ (LocalStrainGradientDensity.continuous_strainGradient chi modes u j).norm.pow 2))
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hright : Integrable (fun x : T3 ↦ (2 / gamma ^ 2) * (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) +
      (800 / gamma ^ 4) * (‖fullVorticity u x‖ ^ 2 *
        (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2))) :=
    (hi.const_mul (2 / gamma ^ 2)).add (hj.const_mul (800 / gamma ^ 4))
  have h := integral_mono (integrable_gradientSquare gamma hg chi modes u hu) hright (fun x ↦ by
    calc
      _ ≤ (2 / gamma ^ 2) * (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) +
          (800 * ‖fullVorticity u x‖ ^ 2 / gamma ^ 4) *
            (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2) :=
        gradientSquare_le gamma hg chi modes u hu x
      _ = _ := by ring)
  change (∫ x : T3, gradientSquare gamma chi modes u x) ≤
    ∫ x : T3, (2 / gamma ^ 2) * (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) +
      (800 / gamma ^ 4) * (‖fullVorticity u x‖ ^ 2 *
        (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2)) at h
  rwa [integral_add (hi.const_mul _) (hj.const_mul _), integral_const_mul, integral_const_mul] at h

end Mettapedia.FluidDynamics.NavierStokes.LocalSquaredGapGradient
