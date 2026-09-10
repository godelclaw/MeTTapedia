import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFourierDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalLowDiffusionBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalFilteredViscousDefect

/-!
# Joint spectral diffusion with the full actual vorticity

The filtered strain Laplacian and full vorticity Laplacian are treated
together. Uniform second differences discharge the spatial diffusion
consistency hypotheses. The actual unforced energy-squared identity pays
the resulting fixed-cutoff cost from initial data.

Only a measurable full-rate envelope is integrated; separate chosen-frame
terms are not assumed measurable. Its nonviscous majorant and integrability
remain explicit, and are not a proved dynamical misalignment budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalJointDiffusionBudget

open scoped Topology Matrix.Norms.Elementwise
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFourierStrainGradient PancakeFilteredStrainDynamics
open PancakeFourierPressureStrain
open PancakeSpatialStrainEvolution PancakePhysicalDiffusionLimit PancakePhysicalLaplacian
open PancakeFourierTranslationCurve PancakeLaplacianDiffusion PancakeRegularizedMaterialRate
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeDyadicDirectionEvolution PancakeHigherDerivativeMoments
open PancakeInfiniteSpatialLaplacian InfiniteKineticCancellation InfiniteConvectionEnergy
open LocalVorticityDiffusion LocalLowDiffusionBudget LocalLowFrequencyBudget LocalKineticEnergy
open PancakeLocalInfiniteVelocity

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def fullCurlSecond (u : FourierVelocity) (j : Fin 3) : T3 → R3 :=
  InfiniteFourierDiffusion.mappedSecond complexRealPartEuclideanCLM (fourierCurl u) j

/-- The ordinary spatial Laplacian of the ordinary full curl. -/
def fullVorticityLaplacian (u : FourierVelocity) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (spatialLaplacian (spatialCurl (fullFourierField id u)) x)

/-- The spatial joint response is exactly the viscous rate in the actual
filtered material identity, evaluated at the same point. -/
theorem jointDiffusionRateAlong_eq {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (delta : ℝ) (X : ℝ → Fin 3 → ℝ) (t : ℝ) :
    LocalFilteredViscousDefect.jointDiffusionRateAlong s chi modes delta X t =
      linearRate (spatialStrain modes (filteredVelocity chi (s.coefficients t)) (torusPoint (X t)))
        delta (fullVorticity (s.coefficients t) (torusPoint (X t)))
        (strainLaplacian modes (filteredVelocity chi (s.coefficients t)) (torusPoint (X t)))
        (fullVorticityLaplacian (s.coefficients t) (torusPoint (X t))) := rfl

theorem summable_secondMoment_curl (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    Summable (fourierMoment 2 (fourierCurl u)) :=
  (hu.mul_left (2 * Real.pi)).of_nonneg_of_le (fourierMoment_nonneg _ _) (fourierMoment_curl_le 2 u)

theorem sum_fullCurlSecond (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (x : T3) :
    (∑ j : Fin 3, fullCurlSecond u j x) = fullVorticityLaplacian u x := by
  have hu1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hu
  have hw2 := summable_secondMoment_curl u hu
  simp only [fullVorticityLaplacian, spatialCurl_velocity u hu1, spatialLaplacian,
    coordinateDerivative2_fullFourierField _ hw2, map_sum, fullCurlSecond,
    InfiniteFourierDiffusion.mappedSecond]

theorem mappedField_curl (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    InfiniteFourierDiffusion.mappedField complexRealPartEuclideanCLM (fourierCurl u) = fullVorticity u := by
  funext x
  simp only [fullVorticity, spatialCurl_velocity u hu, InfiniteFourierDiffusion.mappedField]

/-- The weak spatial diffusion estimate has no receiver truncation. -/
theorem integral_laplacian_diffusion_paid
    (modes : Finset Wavevector) (chi : Wavevector → ℂ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (F R : T3 → ℝ) (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu)
    (hF : Integrable F) (hR : Integrable R)
    (hpoint : ∀ᵐ x : T3, F x ≤ nu * linearRate (spatialStrain modes (filteredVelocity chi u) x)
      delta (fullVorticity u x) (strainLaplacian modes (filteredVelocity chi u) x)
      (fullVorticityLaplacian u x) + R x) :
    (∫ x : T3, F x) ≤ (16 * nu / delta) * (3 * strainGradientAmplitude modes chi u ^ 2) *
      (∫ x : T3, ‖fullVorticity u x‖ ^ 2) + ∫ x : T3, R x := by
  have hu1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hu
  have hw2 := summable_secondMoment_curl u hu
  have hw1 := summable_firstMoment_of_second _ hw2
  have hwI : Summable (indexedFirstMoment id (fourierCurl u)) := by
    simpa only [indexedFirstMoment_id] using hw1
  have hw0 := summable_norm_coefficients id _ hwI
  have hwd := summable_norm_derivativeCoefficients id _ hwI
  have hwdd := summable_norm_secondDerivative _ hw2
  have hS : Continuous (spatialStrain modes (filteredVelocity chi u)) := by
    apply Continuous.subtype_mk
    have hc := PancakeMappedFourierDiffusion.continuous_mappedField realMatrixOperatorCLM modes
      (strainCoeff (filteredVelocity chi u))
    rw [mappedField_strain] at hc
    exact hc
  have hL : 0 ≤ strainGradientAmplitude modes chi u := by
    unfold strainGradientAmplitude
    exact Finset.sum_nonneg (fun q _ ↦ mul_nonneg (strainGradientWeight_nonneg chi q) (norm_nonneg _))
  have hp : ∀ᵐ x : T3, F x ≤ nu * linearRate (spatialStrain modes (filteredVelocity chi u) x)
      delta (fullVorticity u x) (∑ j : Fin 3, strainSecond modes (filteredVelocity chi u) j x)
      (∑ j : Fin 3, fullCurlSecond u j x) + R x := by
    simpa only [sum_fullCurlSecond u hu, strainLaplacian] using hpoint
  have hh := integral_joint_rate_le_of_uniform_approx (Finset.univ : Finset (Fin 3))
    (spatialStrain modes (filteredVelocity chi u)) (fullVorticity u)
    (strainSecond modes (filteredVelocity chi u)) (fullCurlSecond u) F R delta nu
    (fun _ ↦ strainGradientAmplitude modes chi u) coordinateShift
    (fun j ↦ PancakeMappedFourierDiffusion.uniformError modes (strainCoeff (filteredVelocity chi u)) j 9)
    (fun j ↦ InfiniteFourierDiffusion.uniformError (fourierCurl u) j ‖complexRealPartEuclideanCLM‖)
    hd hnu (fun _ _ ↦ hL) hS (continuous_fullVorticity u hu1) hF hR hp
    (fun h _ j _ x ↦ by
      have he := PancakeMappedFourierDiffusion.norm_mappedSecond_sub_central_le realMatrixOperatorCLM modes
        (strainCoeff (filteredVelocity chi u)) j 9 h x (by norm_num) norm_realMatrixOperator_le
      simpa only [mappedField_strain, strainSecond] using he)
    (fun h _ j _ x ↦ by
      have he := InfiniteFourierDiffusion.norm_mappedSecond_sub_central_le complexRealPartEuclideanCLM
        (fourierCurl u) hw0 j h x
      simpa only [mappedField_curl u hu1, fullCurlSecond] using he)
    (fun h _ j _ x ↦ norm_strain_shift_le_amplitude modes chi u j h x)
    (fun h _ j _ x ↦ by
      simpa only [coordinateShift_neg, abs_neg] using norm_strain_shift_le_amplitude modes chi u j (-h) x)
    (fun _ _ ↦ PancakeMappedFourierDiffusion.uniformError_tendsto _ _ _ _)
    (fun j _ ↦ InfiniteFourierDiffusion.uniformError_tendsto _ hw0 j (hwd j) (hwdd j j) _)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using hh

theorem integral_laplacian_diffusion_energy_paid
    (modes : Finset Wavevector) (chi : Wavevector → ℂ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (F R : T3 → ℝ) (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu)
    (hF : Integrable F) (hR : Integrable R)
    (hpoint : ∀ᵐ x : T3, F x ≤ nu * linearRate (spatialStrain modes (filteredVelocity chi u) x)
      delta (fullVorticity u x) (strainLaplacian modes (filteredVelocity chi u) x)
      (fullVorticityLaplacian u x) + R x) :
    (∫ x : T3, F x) ≤ (16 * nu / delta) * strainGradientCutoffWeight modes chi *
      kineticEnergy u * kineticEnergy (fourierCurl u) + ∫ x : T3, R x := by
  apply (integral_laplacian_diffusion_paid modes chi u hu F R delta nu hd hnu hF hR hpoint).trans
  have hu1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hu
  have hE := fullEnergy_le_kineticEnergy modes u (summable_coefficientEnergy u (summable_amplitude u hu1))
  have ha : 3 * strainGradientAmplitude modes chi u ^ 2 ≤
      strainGradientCutoffWeight modes chi * kineticEnergy u := by
    have h := strainGradientAmplitude_sq_le modes modes chi u (fun _ h ↦ h)
    have hh := mul_le_mul_of_nonneg_left hE (strainGradientCutoffWeight_nonneg modes chi)
    unfold strainGradientCutoffWeight at *
    nlinarith
  have hp := mul_le_mul ha (integral_norm_fullVorticity_sq_le u hu1)
    (integral_nonneg (fun _ ↦ sq_nonneg _))
    (mul_nonneg (strainGradientCutoffWeight_nonneg modes chi) (kineticEnergy_nonneg u))
  have hc := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 16 * nu / delta)
  nlinarith

/-- Initial energy pays the full joint diffusion response. The full-rate
and nonviscous integrability hypotheses are retained, not inferred from
the local Fourier envelope near a potentially singular endpoint. -/
theorem spacetime_laplacian_diffusion_le_initial {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 < nu)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (modes : Finset Wavevector) (chi : Wavevector → ℂ) (delta : ℝ) (hd : 0 < delta)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (F R : ℝ → T3 → ℝ)
    (hFx : ∀ τ ∈ Set.Icc (0 : ℝ) t, Integrable (F τ))
    (hRx : ∀ τ ∈ Set.Icc (0 : ℝ) t, Integrable (R τ))
    (hFt : IntervalIntegrable (fun τ ↦ ∫ x : T3, F τ x) volume 0 t)
    (hRt : IntervalIntegrable (fun τ ↦ ∫ x : T3, R τ x) volume 0 t)
    (hpoint : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ᵐ x : T3,
      F τ x ≤ nu * linearRate (spatialStrain modes (filteredVelocity chi (s.coefficients τ)) x)
        delta (fullVorticity (s.coefficients τ) x)
        (strainLaplacian modes (filteredVelocity chi (s.coefficients τ)) x)
        (fullVorticityLaplacian (s.coefficients τ) x) + R τ x) :
    (∫ τ in (0 : ℝ)..t, ∫ x : T3, F τ x) ≤
      4 * strainGradientCutoffWeight modes chi * kineticEnergy u₀ ^ 2 / delta +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, R τ x := by
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hb (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) t) :
      (∫ x : T3, F τ x) - (∫ x : T3, R τ x) ≤
        ((16 * nu / delta) * strainGradientCutoffWeight modes chi) *
          (kineticEnergy (s.coefficients τ) * kineticEnergy (fourierCurl (s.coefficients τ))) := by
    have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ ⟨hτ.1, hτ.2.trans ht.2⟩)
    have h := integral_laplacian_diffusion_energy_paid modes chi _ hm (F τ) (R τ)
      delta nu hd hnu.le (hFx τ hτ) (hRx τ hτ) (hpoint τ hτ)
    nlinarith
  have h := integral_le_of_energy_enstrophy_majorant s hnu g hg hSum hu2 t ht
    (fun τ ↦ (∫ x : T3, F τ x) - ∫ x : T3, R τ x)
    ((16 * nu / delta) * strainGradientCutoffWeight modes chi)
    (mul_nonneg (by positivity) (strainGradientCutoffWeight_nonneg modes chi)) (hFt.sub hRt) hb
  rw [intervalIntegral.integral_sub hFt hRt] at h
  have he : (16 * nu / delta * strainGradientCutoffWeight modes chi) * kineticEnergy u₀ ^ 2 /
      (4 * nu) = 4 * strainGradientCutoffWeight modes chi * kineticEnergy u₀ ^ 2 / delta := by
    field_simp
    ring
  rw [he] at h
  linarith

end Mettapedia.FluidDynamics.NavierStokes.LocalJointDiffusionBudget
