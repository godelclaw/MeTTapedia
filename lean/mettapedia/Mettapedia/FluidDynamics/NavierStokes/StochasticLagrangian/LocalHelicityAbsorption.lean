import Mettapedia.Analysis.WeightedCurlHelicity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedCurlCancellation

/-!
# Radial dissipation pays the longitudinal curl factor

This is an inequality for the actual local solution. It spends half the
radial dissipation in the eighth-moment balance and retains the helicity
square and signed spectral defect. Neither remaining cost is assumed
bounded by the initial data.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalHelicityAbsorption

open MeasureTheory Set
open scoped RealInnerProductSpace
open Mettapedia.Analysis WeightedCurlHelicity
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeFourierMaterialPaths PancakeLocalInfiniteVelocity
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalWeightedCurlCancellation
open LocalVorticityEighthMoment
local notation "T3" => UnitAddTorus (Fin 3)
local instance helicityCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance helicityCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance helicityCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def helicityMoment (u : FourierVelocity) : ℝ :=
  ∫ x : T3, helicityDensity (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)

theorem helicityMoment_nonneg (u : FourierVelocity) : 0 ≤ helicityMoment u :=
  integral_nonneg (fun _ ↦ by unfold helicityDensity; positivity)

theorem helicityMoment_eq (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    helicityMoment u = ∫ x : T3, ‖fullVorticity u x‖ ^ 6 *
      ⟪fullVorticity u x, fullVorticity (fourierCurl u) x⟫ ^ 2 := by
  simp only [helicityMoment, helicityDensity, helicity, fullVorticity_curl_eq_curlJet u hu]

theorem longitudinalHelicityIntegral_eq_jet (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    longitudinalHelicityIntegral u =
      ∫ x : T3, longitudinalDefect (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) := by
  simp only [longitudinalHelicityIntegral, longitudinalDefect, helicity,
    fullVorticity_curl_eq_curlJet u hu]

theorem abs_longitudinalHelicityIntegral_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (η : ℝ) (hη : 0 < η) :
    |longitudinalHelicityIntegral u| ≤ η * radialDissipation u + helicityMoment u / (4 * η) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le _ (by omega : 1 ≤ 2) hu)
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  have hL : Integrable (fun x : T3 ↦ longitudinalDefect (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)) :=
    (continuous_longitudinalDefect _ _ hw hD).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hH : Integrable (fun x : T3 ↦ helicityDensity (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)) :=
    (continuous_helicityDensity _ _ hw hD).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (radialGradientDensity u) :=
    ((hw.norm.pow 4).mul (continuous_finsetSum _ (fun j _ ↦
      (hw.inner (hD j)).pow 2))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [longitudinalHelicityIntegral_eq_jet u hu]
  calc
    _ ≤ ∫ x : T3, |longitudinalDefect (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x : T3, η * radialGradientDensity u x +
        helicityDensity (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) / (4 * η) :=
      integral_mono hL.abs ((hR.const_mul η).add (hH.div_const _))
        (fun x ↦ abs_longitudinalDefect_le _ _ η hη)
    _ = _ := by
      rw [integral_add (hR.const_mul η) (hH.div_const _), integral_const_mul, integral_div]
      rfl

/-- Half of the radial dissipation pays the longitudinal derivative. The
spectral defect stays signed; the helicity moment stays explicit. -/
theorem stretching_add_spectral_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ k, modeDot k (u k) = 0)
    (ν κ : ℝ) (hν : 0 < ν) (hκ : 0 < κ) :
    stretching u + weightedStrainSpectralDefect κ u / κ ≤
      3 * ν * radialDissipation u + 3 / (ν * κ ^ 2) * helicityMoment u := by
  have h := stretching_spectral_identity u hu hd κ
  have he : stretching u + weightedStrainSpectralDefect κ u / κ =
      -(6 / κ) * longitudinalHelicityIntegral u := by
    apply (mul_right_cancel₀ hκ.ne')
    field_simp
    linarith only [h]
  have hL := abs_longitudinalHelicityIntegral_le u
    (summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu) (ν * κ / 2) (by positivity)
  rw [he]
  calc
    _ ≤ 6 / κ * |longitudinalHelicityIntegral u| := by
      have hm := mul_le_mul_of_nonneg_left (neg_le_abs (longitudinalHelicityIntegral u))
        (show 0 ≤ 6 / κ by positivity)
      nlinarith only [hm]
    _ ≤ 6 / κ * (ν * κ / 2 * radialDissipation u + helicityMoment u / (4 * (ν * κ / 2))) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    _ = _ := by field_simp; ring

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients t) q ≤ g q)

include hSum hu in
theorem continuousOn_helicityMoment :
    ContinuousOn (fun t ↦ helicityMoment (s.coefficients t)) (Icc 0 T) := by
  apply LocalAlignmentContinuity.continuousOn_spatialIntegral
  exact continuous_helicityDensity _ _
    (continuous_fullVorticity_spaceTime s g hSum
      (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 4) q).trans (hu t ht q)))
    (fun j ↦ continuous_fullCurlGradient_spaceTime s g hSum
      (fun t ht q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu t ht q)) j)

include hSum hu in
theorem continuousOn_longitudinalHelicityIntegral :
    ContinuousOn (fun t ↦ longitudinalHelicityIntegral (s.coefficients t)) (Icc 0 T) := by
  have hc := LocalAlignmentContinuity.continuousOn_spatialIntegral
    (fun t x ↦ longitudinalDefect (fullVorticity (s.coefficients t) x)
      (fun j ↦ fullCurlGradient (s.coefficients t) j x))
    (continuous_longitudinalDefect _ _
      (continuous_fullVorticity_spaceTime s g hSum
        (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 4) q).trans (hu t ht q)))
      (fun j ↦ continuous_fullCurlGradient_spaceTime s g hSum
        (fun t ht q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu t ht q)) j))
  apply hc.congr
  intro t ht
  exact longitudinalHelicityIntegral_eq_jet _
    (summable_fourierMoment_of_le _ (by omega : 2 ≤ 4)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)))

include hSum hu in
theorem continuousOn_weightedStrainSpectralDefect (κ : ℝ) :
    ContinuousOn (fun t ↦ weightedStrainSpectralDefect κ (s.coefficients t)) (Icc 0 T) := by
  have hc := ((continuousOn_longitudinalHelicityIntegral s g hSum hu).const_mul (-6)).sub
    ((continuousOn_stretching s g hSum
      (fun t ht q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu t ht q))).const_mul κ)
  apply hc.congr
  intro t ht
  have h := stretching_spectral_identity _
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)) (s.transverse t) κ
  dsimp
  linarith only [h]

include hg hSum hu in
/-- The actual initial-endpoint energy inequality after radial absorption.
The spectral contribution is signed, and no bound on either residual
time integral is part of the hypotheses or conclusion. -/
theorem energy_add_spectral_integral_le (hν : 0 < ν) (hT : 0 < T)
    (κ : ℝ) (hκ : 0 < κ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    meanEnergy (s.coefficients t) / 8 +
      ν * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) +
      3 * ν * (∫ τ in (0 : ℝ)..t, radialDissipation (s.coefficients τ)) +
      (∫ τ in (0 : ℝ)..t, weightedStrainSpectralDefect κ (s.coefficients τ)) / κ ≤
        meanEnergy u₀ / 8 + 3 / (ν * κ ^ 2) *
          (∫ τ in (0 : ℝ)..t, helicityMoment (s.coefficients τ)) := by
  have hu3 (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) (q : Wavevector) :=
    (fourierMoment_mono (s.coefficients τ) (by omega : 3 ≤ 4) q).trans (hu τ hτ q)
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hS := ((continuousOn_stretching s g hSum hu3).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hJ := ((continuousOn_weightedStrainSpectralDefect s g hSum hu κ).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hR := ((continuousOn_radialDissipation s g hSum hu3).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hH := ((continuousOn_helicityMoment s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hi := intervalIntegral.integral_mono_on ht.1 (hS.add (hJ.div_const κ))
    ((hR.const_mul (3 * ν)).add (hH.const_mul (3 / (ν * κ ^ 2))))
    (fun τ hτ ↦ stretching_add_spectral_le _
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub hτ)))
      (s.transverse τ) ν κ hν hκ)
  rw [intervalIntegral.integral_add hS (hJ.div_const κ),
    intervalIntegral.integral_add (hR.const_mul _) (hH.const_mul _),
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hi
  have he := energy_identity s g hg hSum hu3 hT t ht
  linarith only [hi, he]

end Mettapedia.FluidDynamics.NavierStokes.LocalHelicityAbsorption
