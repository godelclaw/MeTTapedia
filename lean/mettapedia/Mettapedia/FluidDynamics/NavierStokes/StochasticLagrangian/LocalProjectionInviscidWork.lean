import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpatialVorticityInviscidRate

/-!
# Signed material work of the corrected vorticity energy

The actual inviscid momentum RHS and common spatial transport combine
into strain and the curl-vorticity source. Transport has zero spatial
mean, so the full resolved work is stretching minus the weighted
projection material rate. No estimate or sign for that rate is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalProjectionInviscidWork

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis WeightedProjectionParabolic WeightedProjectionVariation
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeCoefficientLimitEquation PancakeBlockReality
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalWeightedCurlCancellation
open LocalAlignmentForcing LocalVorticitySeparation LocalHelicitySourceEvolution
open LocalHelicityProjectionEvolution LocalWeightedProjectionEvolution
open LocalVorticityEighthMoment FiniteVorticityVariation LocalProjectionSourceWork
open LocalProjectionTransport SpatialVorticityInviscidRate VelocityRHSMoments

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def projectionMaterialRate (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  weightedRate δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
    (fullStrainOperator u x (fullVorticity u x))
    (-gradient u x (fullVorticity (fourierCurl u) x) + source u x)

theorem projectionMaterialRate_eq (δ : ℝ) (u : FourierVelocity) (x : T3) :
    projectionMaterialRate δ u x = amplitudeStrainRate δ u x +
      ‖fullVorticity u x‖ ^ 6 * projectionInviscidRate δ u x := by
  have he := LocalHelicityProjectionEvolution.energyRate_eq δ 0 u x
  simp only [zero_smul, add_zero, zero_mul] at he
  simp only [projectionMaterialRate, weightedRate, he, amplitudeStrainRate,
    LocalHelicityProjectionDiffusion.projectionEnergy]

theorem correctedDensityRate_add_transport (δ κ : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    correctedDensityRate δ κ u (infiniteVelocityRHS 0 u) x +
        correctedTransportRate δ κ u u x =
      stretchingDensity u x - 3 / κ * projectionMaterialRate δ u x := by
  have ha := fullVorticity_inviscidRHS u
    (summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu) hd hr x
  have hb := fullVorticity_curl_inviscidRHS u hu hd hr x
  calc
    _ = ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x,
          fullVorticity (infiniteVelocityRHS 0 u) x + transportVorticity u u x⟫ -
        3 / κ * weightedRate δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
          (fullVorticity (infiniteVelocityRHS 0 u) x + transportVorticity u u x)
          (fullVorticity (fourierCurl (infiniteVelocityRHS 0 u)) x +
            transportVorticity u (fourierCurl u) x) := by
      simp only [correctedDensityRate, densityRate, correctedTransportRate,
        inner_add_right, weightedRate_add]
      ring
    _ = _ := by rw [ha, hb]; rfl

theorem continuous_transportVorticity (u v : FourierVelocity) :
    Continuous (transportVorticity u v) :=
  continuous_finsetSum _ (fun j _ ↦
    (InfiniteFourierTransport.continuous_velocityComponent u j).smul
      (LocalSquaredGapGradient.continuous_fullCurlGradient v j))

theorem continuous_correctedDensityRate (δ κ : ℝ) (hδ : 0 < δ) (u v : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hv : Summable (fourierMoment 2 v)) :
    Continuous (correctedDensityRate δ κ u v) := by
  have ha := continuous_fullVorticity u (summable_firstMoment_of_second u hu)
  have hb := continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu)
  have hf := continuous_fullVorticity v (summable_firstMoment_of_second v hv)
  have hg := continuous_fullVorticity (fourierCurl v) (summable_fourierMoment_curl 1 v hv)
  exact ((ha.norm.pow 6).mul (ha.inner hf)).sub
    ((continuous_weightedRate δ hδ ha hb hf hg).const_mul (3 / κ))

theorem continuous_projectionMaterialRate (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    Continuous (projectionMaterialRate δ u) := by
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hv2 := summable_fourierMoment_infiniteVelocityRHS 2 0 u hu
  have ha := continuous_fullVorticity u (summable_firstMoment_of_second u hu2)
  have hb := continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu2)
  have hf := (continuous_fullVorticity _ (summable_firstMoment_of_second _ hv2)).add
    (continuous_transportVorticity u u)
  have hg := (continuous_fullVorticity _ (summable_fourierMoment_curl 1 _ hv2)).add
    (continuous_transportVorticity u (fourierCurl u))
  have h := continuous_weightedRate δ hδ ha hb hf hg
  change Continuous (fun x : T3 ↦ projectionMaterialRate δ u x)
  simpa only [Pi.add_apply, fullVorticity_inviscidRHS u hu3 hd hr,
    fullVorticity_curl_inviscidRHS u hu hd hr, projectionMaterialRate] using h

/-- The full resolved work, without any extra output restriction. -/
theorem integral_correctedGradient_inviscidRHS (δ κ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 5 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∫ x : T3, ⟪correctedGradient δ κ u x, fullVorticity (infiniteVelocityRHS 0 u) x⟫) =
      stretching u - 3 / κ * ∫ x : T3, projectionMaterialRate δ u x := by
  have hu4 := summable_fourierMoment_of_le _ (by omega : 4 ≤ 5) hu
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 5) hu
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 5) hu
  have hv3 := summable_fourierMoment_infiniteVelocityRHS 3 0 u hu
  have hv2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hv3
  have hiD : Integrable (correctedDensityRate δ κ u (infiniteVelocityRHS 0 u)) :=
    (continuous_correctedDensityRate δ κ hδ u _ hu2 hv2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hiP : Integrable (projectionMaterialRate δ u) :=
    (continuous_projectionMaterialRate δ hδ u hu4 hd hr).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hiS : Integrable (stretchingDensity u) :=
    (continuous_stretchingDensity u hu3).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  obtain ⟨hiT, hzero⟩ := integral_correctedTransportRate_zero δ κ hδ u u hu2 hd hu4
  have he := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall
    (correctedDensityRate_add_transport δ κ u hu4 hd hr))
  rw [integral_add hiD hiT, integral_sub hiS (hiP.const_mul _), integral_const_mul,
    hzero, add_zero, integral_correctedDensityRate_eq δ hδ κ u _ hu4 hv3] at he
  exact he

end Mettapedia.FluidDynamics.NavierStokes.LocalProjectionInviscidWork
