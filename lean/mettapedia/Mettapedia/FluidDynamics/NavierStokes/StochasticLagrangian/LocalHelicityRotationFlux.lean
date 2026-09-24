import Mettapedia.Analysis.SolenoidalRadialPairing
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.HelicitySourceStrainSplit
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalHelicityProjectionEvolution

/-!
# The center-transport debt inside the actual rotational source

The sixth-power-weighted residual paired with the rotation source has
spatial mean exactly one eighth of the existing center-transport integral.
The curl-vorticity leg vanishes by a solenoidal radial flux identity; the
variable-center leg retains its derivative and its sign.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalHelicityRotationFlux

open MeasureTheory Mettapedia.Analysis
open scoped RealInnerProductSpace
open VorticityJetSource LongitudinalHelicityBudget
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeBlockReality
open PancakeFourierTranslationCurve PancakeHaarTransportRate
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalWeightedCurlCancellation
open LocalVariableHelicityCenter LocalHelicityProjectionEvolution
open LocalAlignmentForcing HelicityAngularSource HelicityAngularBudget HelicitySourceStrainSplit

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuous_rotationSource (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (rotationSource u) := by
  have ha := continuous_fullVorticity u hu
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  unfold rotationSource amplitudeGradient
  fun_prop

theorem continuous_strainSource (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (strainSource u) := by
  have hG := continuous_realComponentGradient u hu
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  unfold strainSource VorticityJetSource.source strainRows EuclideanCrossProduct.cross
  fun_prop

theorem continuous_projectionResidual (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    Continuous (projectionResidual δ u) := by
  have ha := continuous_fullVorticity u (summable_firstMoment_of_second u hu)
  have hb := continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu)
  exact hb.sub ((continuous_regularizedCenter δ hδ u hu).smul ha)

theorem integral_curl_rotation_eq_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) :
    (∫ x : T3, ‖fullVorticity u x‖ ^ 6 *
      ⟪fullVorticity (fourierCurl u) x, rotationSource u x⟫) = 0 := by
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu
  have hw3 := summable_fourierMoment_curl 3 u hu
  have h := SolenoidalRadialPairing.integral_radial_pairing_eq_zero
    (fullVorticity u) (fullVorticity (fourierCurl u)) (fullCurlGradient u) (fullCurlGradient (fourierCurl u))
    coordinateShift
    (continuous_fullVorticity u (summable_fourierMoment_of_le _ (by omega : 1 ≤ 4) hu))
    (continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hw3))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u)
    (LocalSquaredGapGradient.continuous_fullCurlGradient (fourierCurl u))
    continuous_coordinateShift coordinateShift_zero
    (hasDerivAt_fullVorticity_shift u hu3) (hasDerivAt_fullVorticity_shift (fourierCurl u) hw3)
    (sum_fullCurlGradient_diagonal_eq_zero (fourierCurl u) hw3) 3
  simpa only [rotationSource, inner_amplitudeGradient, ← pow_mul] using h

def weightedRotationPairing (δ : ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖fullVorticity u x‖ ^ 6 * ⟪projectionResidual δ u x, rotationSource u x⟫

/-- The rotation contribution is an existing signed debt, not an extra
positive error term to be paid separately. -/
theorem weightedRotationPairing_eq (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) :
    weightedRotationPairing δ u = centerTransportIntegral (regularizedCenter δ u) u / 8 := by
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hu1 := summable_firstMoment_of_second u hu2
  have ha := continuous_fullVorticity u hu1
  have hb := continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu2)
  have hg := continuous_rotationSource u hu1
  have hc := continuous_regularizedCenter δ hδ u hu2
  have hI : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 *
      ⟪fullVorticity (fourierCurl u) x, rotationSource u x⟫) :=
    ((ha.norm.pow 6).mul (hb.inner hg)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hK : Integrable (fun x : T3 ↦ regularizedCenter δ u x * (‖fullVorticity u x‖ ^ 6 *
      ⟪fullVorticity u x, rotationSource u x⟫)) :=
    (hc.mul ((ha.norm.pow 6).mul (ha.inner hg))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (x : T3) : ‖fullVorticity u x‖ ^ 6 * ⟪projectionResidual δ u x, rotationSource u x⟫ =
      ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity (fourierCurl u) x, rotationSource u x⟫ -
      regularizedCenter δ u x * (‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x, rotationSource u x⟫) := by
    simp only [projectionResidual, RegularizedProjection.residual, inner_sub_left,
      real_inner_smul_left, regularizedCenter, RegularizedProjection.coefficient]
    ring
  simp only [weightedRotationPairing, he]
  rw [integral_sub hI hK, integral_curl_rotation_eq_zero u hu, zero_sub]
  simp only [rotationSource, inner_amplitudeGradient]
  change -(∫ x : T3, regularizedCenter δ u x * (‖fullVorticity u x‖ ^ 6 *
    longitudinalAmplitude (fullVorticity u x) (fun j ↦ fullCurlGradient u j x))) = _
  rw [integral_center_mul_longitudinal_eq _ u hu3 hc (locallyLipschitz_regularizedCenter δ hδ u hu3)]
  ring

def strainProjectionRate (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  -2 * ⟪projectionResidual δ u x, fullStrainOperator u x (projectionResidual δ u x)⟫ -
    4 * regularizedCenter δ u x * ⟪projectionResidual δ u x, fullStrainOperator u x (fullVorticity u x)⟫ +
    2 * ⟪projectionResidual δ u x, strainSource u x⟫

theorem projectionInviscidRate_eq_strain_add_rotation (δ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    projectionInviscidRate δ u x = strainProjectionRate δ u x +
      2 * ⟪projectionResidual δ u x, rotationSource u x⟫ := by
  rw [projectionInviscidRate_eq, HelicitySourceStrainSplit.source_eq_strain_add_rotation u hu hd hr]
  simp only [strainProjectionRate, inner_add_right]
  ring

theorem continuous_strainProjectionRate (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    Continuous (strainProjectionRate δ u) := by
  have hu1 := summable_firstMoment_of_second u hu
  have hr := continuous_projectionResidual δ hδ u hu
  have ha := continuous_fullVorticity u hu1
  have hc := continuous_regularizedCenter δ hδ u hu
  have hS := continuous_fullStrainOperator u hu1
  have hF := continuous_strainSource u hu1
  exact (((hr.inner (hS.clm_apply hr)).const_mul (-2)).sub
    ((hc.const_mul 4).mul (hr.inner (hS.clm_apply ha)))).add ((hr.inner hF).const_mul 2)

def weightedInviscidRate (δ : ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖fullVorticity u x‖ ^ 6 * projectionInviscidRate δ u x

def weightedStrainRate (δ : ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖fullVorticity u x‖ ^ 6 * strainProjectionRate δ u x

theorem weightedInviscidRate_eq (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    weightedInviscidRate δ u = weightedStrainRate δ u +
      centerTransportIntegral (regularizedCenter δ u) u / 4 := by
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hu1 := summable_firstMoment_of_second u hu2
  have ha := continuous_fullVorticity u hu1
  have hI : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 * strainProjectionRate δ u x) :=
    ((ha.norm.pow 6).mul (continuous_strainProjectionRate δ hδ u hu2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (fun x : T3 ↦ 2 * (‖fullVorticity u x‖ ^ 6 *
      ⟪projectionResidual δ u x, rotationSource u x⟫)) :=
    (((ha.norm.pow 6).mul ((continuous_projectionResidual δ hδ u hu2).inner
      (continuous_rotationSource u hu1))).const_mul 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have he (x : T3) : ‖fullVorticity u x‖ ^ 6 * projectionInviscidRate δ u x =
      ‖fullVorticity u x‖ ^ 6 * strainProjectionRate δ u x +
        2 * (‖fullVorticity u x‖ ^ 6 * ⟪projectionResidual δ u x, rotationSource u x⟫) := by
    rw [projectionInviscidRate_eq_strain_add_rotation δ u hu3 hd hr x]
    ring
  simp only [weightedInviscidRate, he]
  rw [integral_add hI hR, integral_const_mul]
  change weightedStrainRate δ u + 2 * weightedRotationPairing δ u = _
  rw [weightedRotationPairing_eq δ hδ u hu]
  ring

theorem signedRemainder_eq_strain_rates (δ : ℝ) (hδ : 0 < δ) (κ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    LocalRegularizedHelicityBudget.signedRemainder δ κ u =
      weightedStrainSpectralDefect κ u - 3 * weightedInviscidRate δ u + 3 * weightedStrainRate δ u := by
  rw [weightedInviscidRate_eq δ hδ u hu hd hr]
  unfold LocalRegularizedHelicityBudget.signedRemainder
  ring

end Mettapedia.FluidDynamics.NavierStokes.LocalHelicityRotationFlux
