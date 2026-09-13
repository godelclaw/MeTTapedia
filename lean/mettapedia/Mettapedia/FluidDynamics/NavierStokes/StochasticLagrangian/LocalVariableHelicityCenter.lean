import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalCenteredHelicityBudget

/-!
# The signed transport cost of a spatially varying helicity center

Allowing a center to follow local geometry creates a derivative along the
actual vorticity. The exact eighth-moment stretching identity below retains
this signed term. No regularity, smallness, or transport bound for an adaptive
center is inferred from the strain geometry.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalVariableHelicityCenter

open MeasureTheory Mettapedia.Analysis
open scoped RealInnerProductSpace
open WeightedCurlHelicity LongitudinalHelicityBudget CurlHelicityCentering
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakePeriodicVorticityEquation
open PancakeFourierMaterialPaths
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalWeightedCurlCancellation
open LocalHelicityAbsorption

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance variableCenterCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance variableCenterCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance variableCenterCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The center's ordinary translation derivative in the vorticity direction. -/
def longitudinalCenterRate (ρ : T3 → ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, fullVorticity u x j *
    UnitTorusWeakDerivative.shiftRate ρ (UnitTorusWeakDerivative.coordinateShift j) x

def centerTransportIntegral (ρ : T3 → ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖fullVorticity u x‖ ^ 8 * longitudinalCenterRate ρ u x

def centeredIntegral (ρ : T3 → ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, centeredDefect (ρ x) (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)

theorem integral_center_mul_longitudinal_eq (ρ : T3 → ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hρ : Continuous ρ)
    (hρL : LocallyLipschitz (fun r : Fin 3 → ℝ ↦ ρ (UnitTorusWeakDerivative.torusPoint r))) :
    (∫ x : T3, ρ x * (‖fullVorticity u x‖ ^ 6 *
      longitudinalAmplitude (fullVorticity u x) (fun j ↦ fullCurlGradient u j x))) =
        -centerTransportIntegral ρ u / 8 := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hshift (j : Fin 3) : UnitTorusWeakDerivative.coordinateShift j =
      PancakeFourierTranslationCurve.coordinateShift j := by
    funext t i
    simp [UnitTorusWeakDerivative.coordinateShift, UnitTorusWeakDerivative.torusPoint,
      UnitTorusWeakDerivative.coordinateLine, PancakeFourierTranslationCurve.coordinateShift,
      PancakeFourierMaterialPaths.torusPoint, PancakeFourierStrainGradient.coordinateLine]
  have hd (j : Fin 3) (x : T3) : HasDerivAt
      (fun h ↦ fullVorticity u (x + UnitTorusWeakDerivative.coordinateShift j h))
      (fullCurlGradient u j x) 0 := by
    simpa only [hshift, PancakeHaarTransportRate.coordinateShift_zero, add_zero] using
      hasDerivAt_fullVorticity_shift u hu j x 0
  have he := SolenoidalRadialFlux.integral_mul_radial_longitudinal_eq
    (fullVorticity u) (fullCurlGradient u)
    (continuous_fullVorticity u (summable_firstMoment_of_second _ hu2))
    (LocalAlignmentTransport.locallyLipschitz_fullVorticity u hu2) hd
    (sum_fullCurlGradient_diagonal_eq_zero u hu) ρ hρ hρL 3
  norm_num only [← pow_mul, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] at he
  simpa only [div_mul_eq_mul_div, integral_div, neg_div, centerTransportIntegral,
    longitudinalCenterRate] using he

/-- Unlike constant centering, local centering has a longitudinal source. -/
theorem longitudinalHelicityIntegral_eq (ρ : T3 → ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hρ : Continuous ρ)
    (hρL : LocallyLipschitz (fun r : Fin 3 → ℝ ↦ ρ (UnitTorusWeakDerivative.torusPoint r))) :
    longitudinalHelicityIntegral u = centeredIntegral ρ u - centerTransportIntegral ρ u / 8 := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hw := continuous_fullVorticity u (summable_firstMoment_of_second _ hu2)
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  have hL : Integrable (fun x : T3 ↦ longitudinalDefect (fullVorticity u x)
      (fun j ↦ fullCurlGradient u j x)) :=
    (continuous_longitudinalDefect _ _ hw hD).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hP : Integrable (fun x : T3 ↦ ρ x * (‖fullVorticity u x‖ ^ 6 *
      longitudinalAmplitude (fullVorticity u x) (fun j ↦ fullCurlGradient u j x))) :=
    (hρ.mul ((hw.norm.pow 6).mul (continuous_finsetSum _ (fun j _ ↦
      ((PiLp.continuous_apply 2 _ j).comp hw).mul (hw.inner (hD j))))
      )).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp (x : T3) : centeredDefect (ρ x) (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) =
      longitudinalDefect (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) -
        ρ x * (‖fullVorticity u x‖ ^ 6 *
          longitudinalAmplitude (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)) := by
    unfold centeredDefect longitudinalDefect longitudinalAmplitude
    ring
  have he : centeredIntegral ρ u = longitudinalHelicityIntegral u + centerTransportIntegral ρ u / 8 := by
    simp only [centeredIntegral, hp]
    rw [integral_sub hL hP, ← longitudinalHelicityIntegral_eq_jet u hu2,
      integral_center_mul_longitudinal_eq ρ u hu hρ hρL]
    ring
  linarith only [he]

/-- The transport source retains its sign and the exact coefficient `3/4`. -/
theorem stretching_spectral_identity (ρ : T3 → ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hρ : Continuous ρ)
    (hρL : LocallyLipschitz (fun r : Fin 3 → ℝ ↦ ρ (UnitTorusWeakDerivative.torusPoint r))) (κ : ℝ) :
    κ * LocalVorticityEighthMoment.stretching u = -6 * centeredIntegral ρ u +
      3 / 4 * centerTransportIntegral ρ u - weightedStrainSpectralDefect κ u := by
  have he := LocalWeightedCurlCancellation.stretching_spectral_identity u hu hd κ
  rw [longitudinalHelicityIntegral_eq ρ u
    (summable_fourierMoment_of_le u (by omega : 3 ≤ 4) hu) hρ hρL] at he
  linarith only [he]

theorem centerTransportIntegral_const (ρ : ℝ) (u : FourierVelocity) :
    centerTransportIntegral (fun _ ↦ ρ) u = 0 := by
  simp [centerTransportIntegral, longitudinalCenterRate, UnitTorusWeakDerivative.shiftRate]

/-- A concrete spatially adaptive center, regular at zero vorticity. -/
def regularizedCenter (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ⟪fullVorticity u x, fullVorticity (PancakeGalerkinKineticEnergy.fourierCurl u) x⟫ /
    (δ + ‖fullVorticity u x‖ ^ 2)

theorem contDiff_regularized_pair (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ 1 (fun p : R3 × R3 ↦ ⟪p.1, p.2⟫ / (δ + ‖p.1‖ ^ 2)) :=
  (contDiff_fst.inner ℝ contDiff_snd).div
    (contDiff_const.add (contDiff_fst.norm_sq ℝ)) (fun p ↦ by positivity)

theorem continuous_regularizedCenter (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) : Continuous (regularizedCenter δ u) :=
  (contDiff_regularized_pair δ hδ).continuous.comp
    ((continuous_fullVorticity u (summable_firstMoment_of_second _ hu)).prodMk
      (continuous_fullVorticity _ (summable_fourierMoment_curl 1 u hu)))

theorem locallyLipschitz_regularizedCenter (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    LocallyLipschitz (fun r : Fin 3 → ℝ ↦ regularizedCenter δ u (UnitTorusWeakDerivative.torusPoint r)) := by
  have ha : LocallyLipschitz (fun r : Fin 3 → ℝ ↦
      fullVorticity u (UnitTorusWeakDerivative.torusPoint r)) :=
    LocalAlignmentTransport.locallyLipschitz_fullVorticity u
      (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu)
  have hb : LocallyLipschitz (fun r : Fin 3 → ℝ ↦
      fullVorticity (PancakeGalerkinKineticEnergy.fourierCurl u) (UnitTorusWeakDerivative.torusPoint r)) :=
    LocalAlignmentTransport.locallyLipschitz_fullVorticity _ (summable_fourierMoment_curl 2 u hu)
  have hp := ha.prodMk hb
  have hc : LocallyLipschitz (fun p : R3 × R3 ↦ ⟪p.1, p.2⟫ / (δ + ‖p.1‖ ^ 2)) :=
    (contDiff_regularized_pair δ hδ).locallyLipschitz
  simpa only [Function.comp_def, regularizedCenter] using hc.comp hp

theorem helicity_sub_regularizedCenter (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (x : T3) :
    helicity (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) -
        regularizedCenter δ u x * ‖fullVorticity u x‖ ^ 2 =
      δ / (δ + ‖fullVorticity u x‖ ^ 2) *
        helicity (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) := by
  have hden : δ + ‖fullVorticity u x‖ ^ 2 ≠ 0 := by positivity
  simp only [helicity, ← fullVorticity_curl_eq_curlJet u hu x, regularizedCenter]
  field_simp
  ring

/-- The adaptive center reduces the local nonnegative cost, but its signed
longitudinal transport term must also be retained in the stretching identity. -/
theorem centeredDirectionalDensity_regularizedCenter (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (x : T3) :
    centeredDirectionalDensity (regularizedCenter δ u x) (fullVorticity u x)
        (fun j ↦ fullCurlGradient u j x) =
      (δ / (δ + ‖fullVorticity u x‖ ^ 2)) ^ 2 *
        directionalHelicityDensity (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) := by
  rw [centeredDirectionalDensity, helicity_sub_regularizedCenter δ hδ u hu x]
  unfold directionalHelicityDensity
  ring

theorem centeredDirectionalDensity_regularizedCenter_le (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (x : T3) :
    centeredDirectionalDensity (regularizedCenter δ u x) (fullVorticity u x)
        (fun j ↦ fullCurlGradient u j x) ≤
      directionalHelicityDensity (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) := by
  have h0 : 0 ≤ δ / (δ + ‖fullVorticity u x‖ ^ 2) := by positivity
  have h1 : δ / (δ + ‖fullVorticity u x‖ ^ 2) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith [sq_nonneg ‖fullVorticity u x‖]
  rw [centeredDirectionalDensity_regularizedCenter δ hδ u hu x]
  exact mul_le_of_le_one_left (directionalHelicityDensity_nonneg _ _) (by nlinarith)

/-- The adaptive center is constructed from the solution; its continuity and
local Lipschitz regularity are discharged, not additional assumptions. -/
theorem stretching_regularizedCenter_identity (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u))
    (hd : ∀ q, modeDot q (u q) = 0) (κ : ℝ) :
    κ * LocalVorticityEighthMoment.stretching u =
      -6 * centeredIntegral (regularizedCenter δ u) u +
        3 / 4 * centerTransportIntegral (regularizedCenter δ u) u - weightedStrainSpectralDefect κ u :=
  stretching_spectral_identity (regularizedCenter δ u) u hu hd
    (continuous_regularizedCenter δ hδ u (summable_fourierMoment_of_le u (by omega : 2 ≤ 4) hu))
    (locallyLipschitz_regularizedCenter δ hδ u (summable_fourierMoment_of_le u (by omega : 3 ≤ 4) hu)) κ

/-- The spatial derivative remaining after regularized centering. In
particular the derivative of `curl omega` has not disappeared. -/
def regularizedCenterGradient (δ : ℝ) (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  ((⟪fullCurlGradient u j x, fullVorticity (PancakeGalerkinKineticEnergy.fourierCurl u) x⟫ +
      ⟪fullVorticity u x, fullCurlGradient (PancakeGalerkinKineticEnergy.fourierCurl u) j x⟫) *
        (δ + ‖fullVorticity u x‖ ^ 2) -
      ⟪fullVorticity u x, fullVorticity (PancakeGalerkinKineticEnergy.fourierCurl u) x⟫ *
        (2 * ⟪fullVorticity u x, fullCurlGradient u j x⟫)) /
    (δ + ‖fullVorticity u x‖ ^ 2) ^ 2

theorem shiftRate_regularizedCenter (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (j : Fin 3) (x : T3) :
    UnitTorusWeakDerivative.shiftRate (regularizedCenter δ u)
      (UnitTorusWeakDerivative.coordinateShift j) x = regularizedCenterGradient δ u j x := by
  have hshift : UnitTorusWeakDerivative.coordinateShift j =
      PancakeFourierTranslationCurve.coordinateShift j := by
    funext t i
    simp [UnitTorusWeakDerivative.coordinateShift, UnitTorusWeakDerivative.torusPoint,
      UnitTorusWeakDerivative.coordinateLine, PancakeFourierTranslationCurve.coordinateShift,
      PancakeFourierMaterialPaths.torusPoint, PancakeFourierStrainGradient.coordinateLine]
  have ha := hasDerivAt_fullVorticity_shift u
    (summable_fourierMoment_of_le u (by omega : 3 ≤ 4) hu) j x 0
  have hb := hasDerivAt_fullVorticity_shift _ (summable_fourierMoment_curl 3 u hu) j x 0
  have hden : δ + ‖fullVorticity u (x + PancakeFourierTranslationCurve.coordinateShift j 0)‖ ^ 2 ≠ 0 := by
    positivity
  have hd := (ha.inner ℝ hb).fun_div ((hasDerivAt_const 0 δ).fun_add ha.norm_sq) hden
  simpa only [UnitTorusWeakDerivative.shiftRate, hshift, regularizedCenter,
    regularizedCenterGradient, PancakeHaarTransportRate.coordinateShift_zero, add_zero,
    zero_add, add_comm] using hd.deriv

theorem centerTransportIntegral_regularizedCenter_eq (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) :
    centerTransportIntegral (regularizedCenter δ u) u =
      ∫ x : T3, ‖fullVorticity u x‖ ^ 8 *
        (∑ j : Fin 3, fullVorticity u x j * regularizedCenterGradient δ u j x) := by
  simp only [centerTransportIntegral, longitudinalCenterRate, shiftRate_regularizedCenter δ hδ u hu]

end Mettapedia.FluidDynamics.NavierStokes.LocalVariableHelicityCenter
