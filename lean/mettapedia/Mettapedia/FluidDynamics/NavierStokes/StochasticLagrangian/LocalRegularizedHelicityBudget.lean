import Mettapedia.Analysis.RegularizedProjection
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalHelicityCenterEvolution

/-!
# Paying the regularized helicity defect from eighth-moment dissipation

The longitudinal helicity square after regularized centering is bounded by
`delta / 2` times weighted palinstrophy. The spatially varying center's
signed transport term remains in the stretching identity. This payment
does not bound that transport term or the spectral remainder.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRegularizedHelicityBudget

open MeasureTheory Mettapedia.Analysis Set
open scoped RealInnerProductSpace
open WeightedCurlCancellation WeightedCurlHelicity LongitudinalHelicityBudget CurlHelicityCentering
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeFourierMaterialPaths
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalWeightedCurlCancellation
open LocalVariableHelicityCenter LocalHelicityCenterEvolution LocalVorticityEighthMoment
open GaussianRootWeightedIncrement
open PancakeLocalInfiniteVelocity LocalHelicityAbsorption

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem centeredHelicityDensity_le_palinstrophy (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (x : T3) :
    centeredHelicityDensity (regularizedCenter δ u x) (fullVorticity u x)
      (fun j ↦ fullCurlGradient u j x) ≤ δ / 2 * weightedPalinstrophyDensity u x := by
  have hi := RegularizedProjection.inner_residual_sq_le δ hδ
    (fullVorticity u x) (fullVorticity (fourierCurl u) x)
  have he :
      ⟪fullVorticity u x, RegularizedProjection.residual δ (fullVorticity u x)
        (fullVorticity (fourierCurl u) x)⟫ =
      helicity (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) -
        regularizedCenter δ u x * ‖fullVorticity u x‖ ^ 2 := by
    simp only [RegularizedProjection.residual, RegularizedProjection.coefficient,
      inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      regularizedCenter, helicity, ← fullVorticity_curl_eq_curlJet u hu]
  rw [he] at hi
  have hc := norm_curlJet_sq_le (fun j ↦ fullCurlGradient u j x)
  rw [← fullVorticity_curl_eq_curlJet u hu] at hc
  calc
    _ ≤ ‖fullVorticity u x‖ ^ 6 * (δ / 4 * ‖fullVorticity (fourierCurl u) x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ ‖fullVorticity u x‖ ^ 6 * (δ / 4 * (2 * ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2)) := by
      gcongr
    _ = _ := by unfold weightedPalinstrophyDensity; ring

theorem centeredDirectionalDensity_le_palinstrophy (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (x : T3) :
    centeredDirectionalDensity (regularizedCenter δ u x) (fullVorticity u x)
      (fun j ↦ fullCurlGradient u j x) ≤ δ / 2 * weightedPalinstrophyDensity u x :=
  (centeredDirectionalDensity_le _ _ _).trans (centeredHelicityDensity_le_palinstrophy δ hδ u hu x)

theorem abs_centeredDefect_le (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (η : ℝ) (hη : 0 < η) (x : T3) :
    |centeredDefect (regularizedCenter δ u x) (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)| ≤
      η * radialGradientDensity u x + δ / (8 * η) * weightedPalinstrophyDensity u x := by
  apply (CurlHelicityCentering.abs_centeredDefect_le _ _ _ η hη).trans
  change η * radialGradientDensity u x + _ ≤ _
  apply add_le_add le_rfl
  have h := div_le_div_of_nonneg_right (centeredDirectionalDensity_le_palinstrophy δ hδ u hu x)
    (by positivity : 0 ≤ 4 * η)
  exact h.trans_eq (by ring)

theorem abs_centeredIntegral_le (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (η : ℝ) (hη : 0 < η) :
    |centeredIntegral (regularizedCenter δ u) u| ≤
      η * radialDissipation u + δ / (8 * η) * weightedPalinstrophy u := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu
  have hw := continuous_fullVorticity u (summable_firstMoment_of_second _ hu2)
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  have hρ := continuous_regularizedCenter δ hδ u hu2
  have hC : Continuous (fun x : T3 ↦ centeredDefect (regularizedCenter δ u x)
      (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)) :=
    ((hw.norm.pow 4).mul (continuous_finsetSum _ (fun j _ ↦
      ((PiLp.continuous_apply 2 _ j).comp hw).mul (hw.inner (hD j))))).mul
        ((continuous_helicity _ _ hw hD).sub (hρ.mul (hw.norm.pow 2)))
  have hCi : Integrable (fun x : T3 ↦ centeredDefect (regularizedCenter δ u x)
      (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)) :=
    hC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (radialGradientDensity u) :=
    (continuous_radialGradientDensity u hu).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hG : Integrable (weightedPalinstrophyDensity u) :=
    (continuous_weightedPalinstrophyDensity u hu).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x : T3, |centeredDefect (regularizedCenter δ u x) (fullVorticity u x)
        (fun j ↦ fullCurlGradient u j x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x : T3, η * radialGradientDensity u x + δ / (8 * η) * weightedPalinstrophyDensity u x :=
      integral_mono hCi.abs ((hR.const_mul η).add (hG.const_mul _))
        (abs_centeredDefect_le δ hδ u hu2 η hη)
    _ = _ := by
      rw [integral_add (hR.const_mul η) (hG.const_mul _), integral_const_mul, integral_const_mul]
      rfl

/-- Only the centered helicity defect is absorbed. The two signed sources
on the left are not bounded by this theorem. -/
theorem stretching_add_sources_le (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (ν κ : ℝ) (hν : 0 < ν) (hκ : 0 < κ) :
    stretching u + weightedStrainSpectralDefect κ u / κ -
      3 / (4 * κ) * centerTransportIntegral (regularizedCenter δ u) u ≤
        3 * ν * radialDissipation u + 3 * δ / (2 * ν * κ ^ 2) * weightedPalinstrophy u := by
  have hid := stretching_regularizedCenter_identity δ hδ u hu hd κ
  have he : stretching u + weightedStrainSpectralDefect κ u / κ -
      3 / (4 * κ) * centerTransportIntegral (regularizedCenter δ u) u =
      -(6 / κ) * centeredIntegral (regularizedCenter δ u) u := by
    apply (mul_right_cancel₀ hκ.ne')
    field_simp
    linarith only [hid]
  rw [he]
  have hC := abs_centeredIntegral_le δ hδ u
    (summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu) (ν * κ / 2) (by positivity)
  calc
    _ ≤ (6 / κ) * |centeredIntegral (regularizedCenter δ u) u| := by
      have hn := mul_le_mul_of_nonneg_left (neg_le_abs (centeredIntegral (regularizedCenter δ u) u))
        (show 0 ≤ 6 / κ by positivity)
      nlinarith only [hn]
    _ ≤ (6 / κ) * ((ν * κ / 2) * radialDissipation u +
        δ / (8 * (ν * κ / 2)) * weightedPalinstrophy u) :=
      mul_le_mul_of_nonneg_left hC (by positivity)
    _ = _ := by field_simp; ring

/-- Both unpaid signed terms, with their exact relative coefficient. -/
def signedRemainder (δ κ : ℝ) (u : FourierVelocity) : ℝ :=
  weightedStrainSpectralDefect κ u - 3 / 4 * centerTransportIntegral (regularizedCenter δ u) u

theorem signedRemainder_eq (δ : ℝ) (hδ : 0 < δ) (κ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0) :
    signedRemainder δ κ u = -κ * stretching u - 6 * centeredIntegral (regularizedCenter δ u) u := by
  have h := stretching_regularizedCenter_identity δ hδ u hu hd κ
  unfold signedRemainder
  linarith only [h]

theorem stretching_add_remainder_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (ν κ : ℝ) (hν : 0 < ν) (hκ : 0 < κ) :
    stretching u + signedRemainder (ν ^ 2 * κ ^ 2 / 3) κ u / κ ≤
      3 * ν * radialDissipation u + ν / 2 * weightedPalinstrophy u := by
  have h := stretching_add_sources_le (ν ^ 2 * κ ^ 2 / 3) (by positivity) u hu hd ν κ hν hκ
  have he : 3 * (ν ^ 2 * κ ^ 2 / 3) / (2 * ν * κ ^ 2) = ν / 2 := by
    field_simp
  rw [he] at h
  have heL : stretching u + signedRemainder (ν ^ 2 * κ ^ 2 / 3) κ u / κ =
      stretching u + weightedStrainSpectralDefect κ u / κ -
        3 / (4 * κ) * centerTransportIntegral (regularizedCenter (ν ^ 2 * κ ^ 2 / 3) u) u := by
    unfold signedRemainder
    field_simp
    ring
  rw [heL]
  exact h

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients t) q ≤ g q)

include hSum hu in
theorem continuousOn_centeredIntegral (δ : ℝ) (hδ : 0 < δ) :
    ContinuousOn (fun t ↦ centeredIntegral (regularizedCenter δ (s.coefficients t))
      (s.coefficients t)) (Icc 0 T) := by
  have hu2 := fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 4) q).trans (hu t ht q)
  have hu3 := fun t ht q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu t ht q)
  have hw := continuous_fullVorticity_spaceTime s g hSum hu2
  have hD := fun j ↦ continuous_fullCurlGradient_spaceTime s g hSum hu3 j
  have hρ : Continuous (fun z : Icc (0 : ℝ) T × T3 ↦
      regularizedCenter δ (s.coefficients z.1) z.2) := by
    have hc := (continuous_helicity _ _ hw hD).div
      (continuous_const.add (hw.norm.pow 2)) (fun z ↦ by positivity :
        ∀ z : Icc (0 : ℝ) T × T3, δ + ‖fullVorticity (s.coefficients z.1) z.2‖ ^ 2 ≠ 0)
    apply hc.congr
    intro z
    simp only [Pi.div_apply, Pi.add_apply, regularizedCenter, helicity, ← fullVorticity_curl_eq_curlJet _
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu2 z.1 z.1.2))]
  apply LocalAlignmentContinuity.continuousOn_spatialIntegral
  exact ((hw.norm.pow 4).mul (continuous_finsetSum _ (fun j _ ↦
    ((PiLp.continuous_apply 2 _ j).comp hw).mul (hw.inner (hD j))))).mul
      ((continuous_helicity _ _ hw hD).sub (hρ.mul (hw.norm.pow 2)))

include hSum hu in
theorem continuousOn_signedRemainder (δ : ℝ) (hδ : 0 < δ) (κ : ℝ) :
    ContinuousOn (fun t ↦ signedRemainder δ κ (s.coefficients t)) (Icc 0 T) := by
  have hc := ((continuousOn_stretching s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu t ht q))).const_mul (-κ)).sub
      ((continuousOn_centeredIntegral s g hSum hu δ hδ).const_mul 6)
  apply hc.congr
  intro t ht
  exact signedRemainder_eq δ hδ κ _
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)) (s.transverse t)

include hg hSum hu in
/-- The helicity-square cost is paid by existing dissipation. Closing the
proof still requires a lower bound for the time integral of `signedRemainder`. -/
theorem energy_add_remainder_integral_le (hν : 0 < ν) (hT : 0 < T)
    (κ : ℝ) (hκ : 0 < κ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    meanEnergy (s.coefficients t) / 8 +
      ν / 2 * (∫ τ in (0 : ℝ)..t, weightedPalinstrophy (s.coefficients τ)) +
      3 * ν * (∫ τ in (0 : ℝ)..t, radialDissipation (s.coefficients τ)) +
      (∫ τ in (0 : ℝ)..t, signedRemainder (ν ^ 2 * κ ^ 2 / 3) κ (s.coefficients τ)) / κ ≤
        meanEnergy u₀ / 8 := by
  have hu3 := fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu τ hτ q)
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hS := ((continuousOn_stretching s g hSum hu3).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hJ := ((continuousOn_signedRemainder s g hSum hu (ν ^ 2 * κ ^ 2 / 3)
    (by positivity) κ).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
  have hR := ((continuousOn_radialDissipation s g hSum hu3).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hG := ((continuousOn_weightedPalinstrophy s g hSum hu3).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have hi := intervalIntegral.integral_mono_on ht.1 (hS.add (hJ.div_const κ))
    ((hR.const_mul (3 * ν)).add (hG.const_mul (ν / 2)))
    (fun τ hτ ↦ stretching_add_remainder_le _
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub hτ))) (s.transverse τ) ν κ hν hκ)
  rw [intervalIntegral.integral_add hS (hJ.div_const κ),
    intervalIntegral.integral_add (hR.const_mul _) (hG.const_mul _),
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hi
  have he := energy_identity s g hg hSum hu3 hT t ht
  linarith only [hi, he]

end Mettapedia.FluidDynamics.NavierStokes.LocalRegularizedHelicityBudget
