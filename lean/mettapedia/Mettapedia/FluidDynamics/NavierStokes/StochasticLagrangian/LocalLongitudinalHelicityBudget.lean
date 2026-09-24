import Mettapedia.Analysis.LongitudinalHelicityBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalHelicityAbsorption

/-!
# Longitudinal coherence in the actual helicity budget

The radial absorption is applied before discarding the angle between
vorticity and its amplitude gradient. The resulting measurable cost is
bounded by the previous helicity moment and vanishes under exact
longitudinal depletion. Its time integral remains a dynamical obligation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalLongitudinalHelicityBudget

open MeasureTheory Set
open scoped RealInnerProductSpace
open Mettapedia.Analysis WeightedCurlHelicity LongitudinalHelicityBudget
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeFourierMaterialPaths PancakeLocalInfiniteVelocity
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalWeightedCurlCancellation
open LocalVorticityEighthMoment LocalHelicityAbsorption
local notation "T3" => UnitAddTorus (Fin 3)
local instance longitudinalCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance longitudinalCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance longitudinalCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def directionalHelicityMoment (u : FourierVelocity) : ℝ :=
  ∫ x : T3, directionalHelicityDensity (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)

theorem directionalHelicityMoment_nonneg (u : FourierVelocity) :
    0 ≤ directionalHelicityMoment u := integral_nonneg (fun _ ↦ directionalHelicityDensity_nonneg _ _)

theorem integrable_directionalHelicityDensity (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    Integrable (fun x : T3 ↦ directionalHelicityDensity (fullVorticity u x)
      (fun j ↦ fullCurlGradient u j x)) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le _ (by omega : 1 ≤ 2) hu)
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  have hH : Integrable (fun x : T3 ↦ helicityDensity (fullVorticity u x)
      (fun j ↦ fullCurlGradient u j x)) :=
    (continuous_helicityDensity _ _ hw hD).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply hH.mono' (measurable_directionalHelicityDensity _ _ hw hD).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x ↦ by
    rw [Real.norm_of_nonneg (directionalHelicityDensity_nonneg _ _)]
    exact directionalHelicityDensity_le _ _)

theorem directionalHelicityMoment_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) : directionalHelicityMoment u ≤ helicityMoment u := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le _ (by omega : 1 ≤ 2) hu)
  have hH : Integrable (fun x : T3 ↦ helicityDensity (fullVorticity u x)
      (fun j ↦ fullCurlGradient u j x)) :=
    (continuous_helicityDensity _ _ hw (LocalSquaredGapGradient.continuous_fullCurlGradient u)
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact integral_mono (integrable_directionalHelicityDensity u hu) hH
    (fun _ ↦ directionalHelicityDensity_le _ _)

theorem directionalHelicityMoment_eq_zero_of_no_longitudinal_variation (u : FourierVelocity)
    (h : ∀ x : T3, ∑ j : Fin 3, fullVorticity u x j *
      ⟪fullVorticity u x, fullCurlGradient u j x⟫ = 0) :
    directionalHelicityMoment u = 0 := by
  unfold directionalHelicityMoment
  have hz (x : T3) := directionalHelicityDensity_eq_zero_of_longitudinalAmplitude_eq_zero
    (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) (h x)
  simp only [hz, integral_zero]

theorem abs_longitudinalHelicityIntegral_le_directional (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (η : ℝ) (hη : 0 < η) :
    |longitudinalHelicityIntegral u| ≤ η * radialDissipation u +
      directionalHelicityMoment u / (4 * η) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le _ (by omega : 1 ≤ 2) hu)
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  have hL : Integrable (fun x : T3 ↦ longitudinalDefect (fullVorticity u x)
      (fun j ↦ fullCurlGradient u j x)) :=
    (continuous_longitudinalDefect _ _ hw hD).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (radialGradientDensity u) :=
    ((hw.norm.pow 4).mul (continuous_finsetSum _ (fun j _ ↦
      (hw.inner (hD j)).pow 2))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hK := integrable_directionalHelicityDensity u hu
  rw [longitudinalHelicityIntegral_eq_jet u hu]
  calc
    _ ≤ ∫ x : T3, |longitudinalDefect (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x : T3, η * radialGradientDensity u x +
        directionalHelicityDensity (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) / (4 * η) :=
      integral_mono hL.abs ((hR.const_mul η).add (hK.div_const _))
        (fun x ↦ LongitudinalHelicityBudget.abs_longitudinalDefect_le _ _ η hη)
    _ = _ := by
      rw [integral_add (hR.const_mul η) (hK.div_const _), integral_const_mul, integral_div]
      rfl

/-- This is proved from the sharper pointwise absorption, not by decreasing
the right side of an already established coarser inequality. -/
theorem stretching_add_spectral_le_directional (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ k, modeDot k (u k) = 0)
    (ν κ : ℝ) (hν : 0 < ν) (hκ : 0 < κ) :
    stretching u + weightedStrainSpectralDefect κ u / κ ≤
      3 * ν * radialDissipation u + 3 / (ν * κ ^ 2) * directionalHelicityMoment u := by
  have h := stretching_spectral_identity u hu hd κ
  have he : stretching u + weightedStrainSpectralDefect κ u / κ =
      -(6 / κ) * longitudinalHelicityIntegral u := by
    apply (mul_right_cancel₀ hκ.ne')
    field_simp
    linarith only [h]
  have hL := abs_longitudinalHelicityIntegral_le_directional u
    (summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu) (ν * κ / 2) (by positivity)
  rw [he]
  calc
    _ ≤ 6 / κ * |longitudinalHelicityIntegral u| := by
      have hm := mul_le_mul_of_nonneg_left (neg_le_abs (longitudinalHelicityIntegral u))
        (show 0 ≤ 6 / κ by positivity)
      nlinarith only [hm]
    _ ≤ 6 / κ * (ν * κ / 2 * radialDissipation u + directionalHelicityMoment u / (4 * (ν * κ / 2))) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    _ = _ := by field_simp; ring

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients t) q ≤ g q)

include hSum hu in
theorem measurable_directionalHelicityDensity_spaceTime :
    Measurable (fun z : Icc (0 : ℝ) T × T3 ↦
      directionalHelicityDensity (fullVorticity (s.coefficients z.1) z.2)
        (fun j ↦ fullCurlGradient (s.coefficients z.1) j z.2)) :=
  measurable_directionalHelicityDensity _ _
    (continuous_fullVorticity_spaceTime s g hSum
      (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 4) q).trans (hu t ht q)))
    (fun j ↦ continuous_fullCurlGradient_spaceTime s g hSum
      (fun t ht q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu t ht q)) j)

include hSum hu in
theorem intervalIntegrable_directionalHelicityMoment (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ directionalHelicityMoment (s.coefficients τ)) volume 0 t := by
  have hm := (measurable_directionalHelicityDensity_spaceTime s g hSum hu
    ).stronglyMeasurable.integral_prod_right' (ν := (volume : Measure T3))
  have hmr : AEStronglyMeasurable (fun τ ↦ directionalHelicityMoment (s.coefficients τ))
      (volume.restrict (Icc (0 : ℝ) T)) :=
    ((aemeasurable_restrict_iff_comap_subtype measurableSet_Icc).mpr
      hm.measurable.aemeasurable).aestronglyMeasurable
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hmem : uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) t := by
    rw [uIoc_of_le ht.1]
    exact Ioc_subset_Icc_self
  have hH := ((continuousOn_helicityMoment s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  apply hH.mono_fun' (hmr.mono_measure (Measure.restrict_mono (hmem.trans hsub) le_rfl))
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with τ hτ
  rw [Real.norm_of_nonneg (directionalHelicityMoment_nonneg _)]
  exact directionalHelicityMoment_le _ (summable_fourierMoment_of_le _ (by omega : 2 ≤ 4)
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub (hmem hτ)))))

include hg hSum hu in
/-- The sharper actual initial-endpoint inequality. It retains amplitude
direction coherence without assuming that coherence stays small. -/
theorem energy_add_spectral_integral_le_directional (hν : 0 < ν) (hT : 0 < T)
    (κ : ℝ) (hκ : 0 < κ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    meanEnergy (s.coefficients t) / 8 +
      ν * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) +
      3 * ν * (∫ τ in (0 : ℝ)..t, radialDissipation (s.coefficients τ)) +
      (∫ τ in (0 : ℝ)..t, weightedStrainSpectralDefect κ (s.coefficients τ)) / κ ≤
        meanEnergy u₀ / 8 + 3 / (ν * κ ^ 2) *
          (∫ τ in (0 : ℝ)..t, directionalHelicityMoment (s.coefficients τ)) := by
  have hu3 (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) (q : Wavevector) :=
    (fourierMoment_mono (s.coefficients τ) (by omega : 3 ≤ 4) q).trans (hu τ hτ q)
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hS := ((continuousOn_stretching s g hSum hu3).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hJ := ((continuousOn_weightedStrainSpectralDefect s g hSum hu κ).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hR := ((continuousOn_radialDissipation s g hSum hu3).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hK := intervalIntegrable_directionalHelicityMoment s g hSum hu t ht
  have hi := intervalIntegral.integral_mono_on ht.1 (hS.add (hJ.div_const κ))
    ((hR.const_mul (3 * ν)).add (hK.const_mul (3 / (ν * κ ^ 2))))
    (fun τ hτ ↦ stretching_add_spectral_le_directional _
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub hτ)))
      (s.transverse τ) ν κ hν hκ)
  rw [intervalIntegral.integral_add hS (hJ.div_const κ),
    intervalIntegral.integral_add (hR.const_mul _) (hK.const_mul _),
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hi
  have he := energy_identity s g hg hSum hu3 hT t ht
  linarith only [hi, he]

end Mettapedia.FluidDynamics.NavierStokes.LocalLongitudinalHelicityBudget
