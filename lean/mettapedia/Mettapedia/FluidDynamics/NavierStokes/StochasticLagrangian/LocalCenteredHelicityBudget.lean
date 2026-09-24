import Mettapedia.Analysis.CurlHelicityCentering
import Mettapedia.Analysis.SolenoidalRadialFlux
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalLongitudinalHelicityBudget

/-!
# Centered helicity in the actual signed energy budget

Solenoidal radial flux has zero mean. Consequently the signed defect is
unchanged by subtracting a spatially constant multiple of squared
vorticity from curl helicity. The resulting budget retains both this
centering and longitudinal amplitude-direction depletion. No bound on
their evolution is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalCenteredHelicityBudget

open MeasureTheory Set
open scoped RealInnerProductSpace
open Mettapedia.Analysis WeightedCurlHelicity LongitudinalHelicityBudget CurlHelicityCentering
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeFourierMaterialPaths PancakeLocalInfiniteVelocity
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalWeightedCurlCancellation
open LocalVorticityEighthMoment LocalHelicityAbsorption LocalLongitudinalHelicityBudget
local notation "T3" => UnitAddTorus (Fin 3)
local instance centeredCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance centeredCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance centeredCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_radial_longitudinal_eq_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (n : ℕ) :
    (∫ x : T3, (‖fullVorticity u x‖ ^ 2) ^ n *
      longitudinalAmplitude (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)) = 0 := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hshift (j : Fin 3) : UnitTorusWeakDerivative.coordinateShift j =
      PancakeFourierTranslationCurve.coordinateShift j := by
    funext t i
    simp [UnitTorusWeakDerivative.coordinateShift, UnitTorusWeakDerivative.torusPoint,
      UnitTorusWeakDerivative.coordinateLine, PancakeFourierTranslationCurve.coordinateShift,
      PancakeFourierMaterialPaths.torusPoint, PancakeFourierStrainGradient.coordinateLine]
  apply SolenoidalRadialFlux.integral_radial_longitudinal_eq_zero
    (fullVorticity u) (fullCurlGradient u)
    (continuous_fullVorticity u (summable_firstMoment_of_second _ hu2))
    (LocalAlignmentTransport.locallyLipschitz_fullVorticity u hu2)
  · intro j x
    simpa only [hshift, PancakeHaarTransportRate.coordinateShift_zero, add_zero] using
      hasDerivAt_fullVorticity_shift u hu j x 0
  · exact sum_fullCurlGradient_diagonal_eq_zero u hu

def centeredDirectionalMoment (ρ : ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, centeredDirectionalDensity ρ (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)

def centeredHelicityMoment (ρ : ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, centeredHelicityDensity ρ (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)

theorem centeredDirectionalMoment_nonneg (ρ : ℝ) (u : FourierVelocity) :
    0 ≤ centeredDirectionalMoment ρ u := integral_nonneg (fun _ ↦ centeredDirectionalDensity_nonneg _ _ _)

theorem centeredDirectionalMoment_zero (u : FourierVelocity) :
    centeredDirectionalMoment 0 u = directionalHelicityMoment u := by
  simp only [centeredDirectionalMoment, centeredDirectionalDensity_zero, directionalHelicityMoment]

theorem centeredHelicityMoment_eq (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    centeredHelicityMoment ρ u = ∫ x : T3, ‖fullVorticity u x‖ ^ 6 *
      ⟪fullVorticity u x, fullVorticity (fourierCurl u) x - ρ • fullVorticity u x⟫ ^ 2 := by
  simp only [centeredHelicityMoment, centeredHelicityDensity, helicity,
    fullVorticity_curl_eq_curlJet u hu, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]

theorem integrable_centeredHelicityDensity (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    Integrable (fun x : T3 ↦ centeredHelicityDensity ρ (fullVorticity u x)
      (fun j ↦ fullCurlGradient u j x)) :=
  (continuous_centeredHelicityDensity ρ _ _
    (continuous_fullVorticity u (summable_fourierMoment_of_le _ (by omega : 1 ≤ 2) hu))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u)
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_centeredDirectionalDensity (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    Integrable (fun x : T3 ↦ centeredDirectionalDensity ρ (fullVorticity u x)
      (fun j ↦ fullCurlGradient u j x)) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le _ (by omega : 1 ≤ 2) hu)
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  apply (integrable_centeredHelicityDensity ρ u hu).mono'
    (measurable_centeredDirectionalDensity ρ _ _ hw hD).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x ↦ by
    rw [Real.norm_of_nonneg (centeredDirectionalDensity_nonneg _ _ _)]
    exact centeredDirectionalDensity_le _ _ _)

theorem centeredDirectionalMoment_le (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    centeredDirectionalMoment ρ u ≤ centeredHelicityMoment ρ u :=
  integral_mono (integrable_centeredDirectionalDensity ρ u hu)
    (integrable_centeredHelicityDensity ρ u hu) (fun _ ↦ centeredDirectionalDensity_le _ _ _)

/-- This is cancellation after spatial integration, not a pointwise identity. -/
theorem integral_centeredDefect_eq (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T3, centeredDefect ρ (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)) =
      longitudinalHelicityIntegral u := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu
  have hw := continuous_fullVorticity u (summable_firstMoment_of_second _ hu2)
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  have hL : Integrable (fun x : T3 ↦ longitudinalDefect (fullVorticity u x)
      (fun j ↦ fullCurlGradient u j x)) :=
    (continuous_longitudinalDefect _ _ hw hD).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hP : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 *
      longitudinalAmplitude (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)) :=
    ((hw.norm.pow 6).mul (continuous_finsetSum _ (fun j _ ↦
      ((PiLp.continuous_apply 2 _ j).comp hw).mul (hw.inner (hD j))))
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hzero : (∫ x : T3, ‖fullVorticity u x‖ ^ 6 *
      longitudinalAmplitude (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)) = 0 := by
    simpa only [← pow_mul] using integral_radial_longitudinal_eq_zero u hu 3
  have he (a : EuclideanSpace ℝ (Fin 3)) (D : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
      centeredDefect ρ a D = longitudinalDefect a D - ρ * (‖a‖ ^ 6 * longitudinalAmplitude a D) := by
    unfold centeredDefect longitudinalDefect longitudinalAmplitude
    ring
  simp_rw [he]
  rw [integral_sub hL (hP.const_mul ρ), integral_const_mul, hzero, mul_zero, sub_zero]
  exact (longitudinalHelicityIntegral_eq_jet u hu2).symm

theorem abs_longitudinalHelicityIntegral_le_centered (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (η : ℝ) (hη : 0 < η) :
    |longitudinalHelicityIntegral u| ≤ η * radialDissipation u +
      centeredDirectionalMoment ρ u / (4 * η) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hu)
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  have hL : Integrable (fun x : T3 ↦ centeredDefect ρ (fullVorticity u x)
      (fun j ↦ fullCurlGradient u j x)) :=
    (continuous_centeredDefect ρ _ _ hw hD).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (radialGradientDensity u) :=
    (continuous_radialGradientDensity u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hK := integrable_centeredDirectionalDensity ρ u
    (summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu)
  rw [← integral_centeredDefect_eq ρ u hu]
  calc
    _ ≤ ∫ x : T3, |centeredDefect ρ (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x : T3, η * radialGradientDensity u x +
        centeredDirectionalDensity ρ (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) / (4 * η) :=
      integral_mono hL.abs ((hR.const_mul η).add (hK.div_const _))
        (fun x ↦ abs_centeredDefect_le ρ _ _ η hη)
    _ = _ := by
      rw [integral_add (hR.const_mul η) (hK.div_const _), integral_const_mul, integral_div]
      rfl

theorem stretching_add_spectral_le_centered (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ k, modeDot k (u k) = 0)
    (ν κ : ℝ) (hν : 0 < ν) (hκ : 0 < κ) :
    stretching u + weightedStrainSpectralDefect κ u / κ ≤
      3 * ν * radialDissipation u + 3 / (ν * κ ^ 2) * centeredDirectionalMoment ρ u := by
  have h := stretching_spectral_identity u hu hd κ
  have he : stretching u + weightedStrainSpectralDefect κ u / κ =
      -(6 / κ) * longitudinalHelicityIntegral u := by
    apply (mul_right_cancel₀ hκ.ne')
    field_simp
    linarith only [h]
  have hL := abs_longitudinalHelicityIntegral_le_centered ρ u
    (summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu) (ν * κ / 2) (by positivity)
  rw [he]
  calc
    _ ≤ 6 / κ * |longitudinalHelicityIntegral u| := by
      have hm := mul_le_mul_of_nonneg_left (neg_le_abs (longitudinalHelicityIntegral u))
        (show 0 ≤ 6 / κ by positivity)
      nlinarith only [hm]
    _ ≤ 6 / κ * (ν * κ / 2 * radialDissipation u + centeredDirectionalMoment ρ u / (4 * (ν * κ / 2))) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    _ = _ := by field_simp; ring

theorem centeredDirectionalMoment_eq_zero_of_curl_eigenfield (ρ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hc : ∀ x : T3, fullVorticity (fourierCurl u) x = ρ • fullVorticity u x) :
    centeredDirectionalMoment ρ u = 0 := by
  have hz (x : T3) := centeredDirectionalDensity_eq_zero_of_curl_eq ρ (fullVorticity u x)
    (fun j ↦ fullCurlGradient u j x) ((fullVorticity_curl_eq_curlJet u hu x).symm.trans (hc x))
  simp only [centeredDirectionalMoment, hz, integral_zero]

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients t) q ≤ g q)

include hSum hu in
theorem continuousOn_centeredHelicityMoment (ρ : ℝ) :
    ContinuousOn (fun t ↦ centeredHelicityMoment ρ (s.coefficients t)) (Icc 0 T) := by
  apply LocalAlignmentContinuity.continuousOn_spatialIntegral
  exact continuous_centeredHelicityDensity ρ _ _
    (continuous_fullVorticity_spaceTime s g hSum
      (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 4) q).trans (hu t ht q)))
    (fun j ↦ continuous_fullCurlGradient_spaceTime s g hSum
      (fun t ht q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu t ht q)) j)

include hSum hu in
theorem measurable_centeredDirectionalDensity_spaceTime (ρ : ℝ) :
    Measurable (fun z : Icc (0 : ℝ) T × T3 ↦
      centeredDirectionalDensity ρ (fullVorticity (s.coefficients z.1) z.2)
        (fun j ↦ fullCurlGradient (s.coefficients z.1) j z.2)) :=
  measurable_centeredDirectionalDensity ρ _ _
    (continuous_fullVorticity_spaceTime s g hSum
      (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 4) q).trans (hu t ht q)))
    (fun j ↦ continuous_fullCurlGradient_spaceTime s g hSum
      (fun t ht q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu t ht q)) j)

include hSum hu in
theorem intervalIntegrable_centeredDirectionalMoment (ρ : ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ centeredDirectionalMoment ρ (s.coefficients τ)) volume 0 t := by
  have hm := (measurable_centeredDirectionalDensity_spaceTime s g hSum hu ρ
    ).stronglyMeasurable.integral_prod_right' (ν := (volume : Measure T3))
  have hmr : AEStronglyMeasurable (fun τ ↦ centeredDirectionalMoment ρ (s.coefficients τ))
      (volume.restrict (Icc (0 : ℝ) T)) :=
    ((aemeasurable_restrict_iff_comap_subtype measurableSet_Icc).mpr
      hm.measurable.aemeasurable).aestronglyMeasurable
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hmem : uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) t := by
    rw [uIoc_of_le ht.1]
    exact Ioc_subset_Icc_self
  have hH := ((continuousOn_centeredHelicityMoment s g hSum hu ρ).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  apply hH.mono_fun' (hmr.mono_measure (Measure.restrict_mono (hmem.trans hsub) le_rfl))
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with τ hτ
  rw [Real.norm_of_nonneg (centeredDirectionalMoment_nonneg _ _)]
  exact centeredDirectionalMoment_le ρ _ (summable_fourierMoment_of_le _ (by omega : 2 ≤ 4)
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub (hmem hτ)))))

include hg hSum hu in
/-- The centering parameter is spatially and temporally constant here.
Neither the centered cost nor the signed spectral term has an assumed
initial-data budget. -/
theorem energy_add_spectral_integral_le_centered (hν : 0 < ν) (hT : 0 < T)
    (ρ κ : ℝ) (hκ : 0 < κ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    meanEnergy (s.coefficients t) / 8 +
      ν * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) +
      3 * ν * (∫ τ in (0 : ℝ)..t, radialDissipation (s.coefficients τ)) +
      (∫ τ in (0 : ℝ)..t, weightedStrainSpectralDefect κ (s.coefficients τ)) / κ ≤
        meanEnergy u₀ / 8 + 3 / (ν * κ ^ 2) *
          (∫ τ in (0 : ℝ)..t, centeredDirectionalMoment ρ (s.coefficients τ)) := by
  have hu3 (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) (q : Wavevector) :=
    (fourierMoment_mono (s.coefficients τ) (by omega : 3 ≤ 4) q).trans (hu τ hτ q)
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hS := ((continuousOn_stretching s g hSum hu3).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hJ := ((continuousOn_weightedStrainSpectralDefect s g hSum hu κ).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hR := ((continuousOn_radialDissipation s g hSum hu3).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hK := intervalIntegrable_centeredDirectionalMoment s g hSum hu ρ t ht
  have hi := intervalIntegral.integral_mono_on ht.1 (hS.add (hJ.div_const κ))
    ((hR.const_mul (3 * ν)).add (hK.const_mul (3 / (ν * κ ^ 2))))
    (fun τ hτ ↦ stretching_add_spectral_le_centered ρ _
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub hτ)))
      (s.transverse τ) ν κ hν hκ)
  rw [intervalIntegral.integral_add hS (hJ.div_const κ),
    intervalIntegral.integral_add (hR.const_mul _) (hK.const_mul _),
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hi
  have he := energy_identity s g hg hSum hu3 hT t ht
  linarith only [hi, he]

end Mettapedia.FluidDynamics.NavierStokes.LocalCenteredHelicityBudget
