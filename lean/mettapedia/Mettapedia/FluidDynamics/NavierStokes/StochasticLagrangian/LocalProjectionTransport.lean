import Mettapedia.Analysis.WeightedProjectionRegularity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredProjectionNonlinearWork

/-!
# Exact transport cancellation for the corrected projection density

The advecting velocity is an actual divergence-free Fourier field. The
transported vorticity and curl vorticity come from one other field. Their
joint transport is the ordinary scalar transport of the corrected density,
and its spatial integral is zero. No strain or subgrid source is discarded.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalProjectionTransport

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis WeightedProjectionParabolic WeightedProjectionVariation
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeFourierMaterialPaths PancakeHaarTransportRate
open PancakeFourierTranslationCurve PancakePeriodicWeakDerivative PancakeWeakIncompressibleTransport
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalWeightedCurlCancellation
open LocalWeightedProjectionEvolution FiniteVorticityVariation

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def transportVorticity (u v : FourierVelocity) (x : T3) : R3 :=
  ∑ j : Fin 3, InfiniteFourierTransport.velocityComponent u j x • fullCurlGradient v j x

def correctedTransportRate (δ κ : ℝ) (u v : FourierVelocity) (x : T3) : ℝ :=
  ‖fullVorticity v x‖ ^ 6 * ⟪fullVorticity v x, transportVorticity u v x⟫ -
    3 / κ * weightedRate δ (fullVorticity v x) (fullVorticity (fourierCurl v) x)
      (transportVorticity u v x) (transportVorticity u (fourierCurl v) x)

theorem continuous_correctedDensity (δ κ : ℝ) (hδ : 0 < δ) (v : FourierVelocity)
    (hv : Summable (fourierMoment 2 v)) : Continuous (correctedDensity δ κ v) := by
  change Continuous (fun x : T3 ↦ correctedDensity δ κ v x)
  have h := (WeightedProjectionRegularity.contDiff_correctedEnergy (E := R3) δ κ hδ).continuous.comp
    ((continuous_fullVorticity v (summable_firstMoment_of_second v hv)).prodMk
      (continuous_fullVorticity _ (summable_fourierMoment_curl 1 v hv)))
  simpa only [Function.comp_def, correctedDensity, weightedProjectionDensity,
    LocalHelicityProjectionDiffusion.projectionEnergy, weightedEnergy] using h

theorem locallyLipschitz_correctedDensity (δ κ : ℝ) (hδ : 0 < δ) (v : FourierVelocity)
    (hv : Summable (fourierMoment 3 v)) :
    LocallyLipschitz (fun r : X3 ↦ correctedDensity δ κ v (torusPoint r)) := by
  have h := (WeightedProjectionRegularity.contDiff_correctedEnergy (E := R3) δ κ hδ).locallyLipschitz.comp
    ((LocalAlignmentTransport.locallyLipschitz_fullVorticity v
      (summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hv)).prodMk
      (LocalAlignmentTransport.locallyLipschitz_fullVorticity _ (summable_fourierMoment_curl 2 v hv)))
  simpa only [Function.comp_def, correctedDensity, weightedProjectionDensity,
    LocalHelicityProjectionDiffusion.projectionEnergy, weightedEnergy] using h

theorem shiftRate_correctedDensity (δ κ : ℝ) (hδ : 0 < δ) (v : FourierVelocity)
    (hv : Summable (fourierMoment 4 v)) (j : Fin 3) (x : T3) :
    shiftRate (correctedDensity δ κ v) (coordinateShift j) x =
      ‖fullVorticity v x‖ ^ 6 * ⟪fullVorticity v x, fullCurlGradient v j x⟫ -
        3 / κ * weightedRate δ (fullVorticity v x) (fullVorticity (fourierCurl v) x)
          (fullCurlGradient v j x) (fullCurlGradient (fourierCurl v) j x) := by
  have ha := hasDerivAt_fullVorticity_shift v (summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hv) j x 0
  have hb := hasDerivAt_fullVorticity_shift (fourierCurl v) (summable_fourierMoment_curl 3 v hv) j x 0
  have hk := hasDerivAt_weightedEnergy δ hδ ha hb
  have h := (((ha.norm_sq.fun_pow 4).div_const 8).sub (hk.const_mul (3 / κ)))
  simp only [← pow_mul, Nat.reduceMul] at h
  change HasDerivAt (fun t ↦ correctedDensity δ κ v (x + coordinateShift j t)) _ 0 at h
  rw [show shiftRate (correctedDensity δ κ v) (coordinateShift j) x =
    deriv (fun t ↦ correctedDensity δ κ v (x + coordinateShift j t)) 0 from rfl, h.deriv]
  simp only [coordinateShift_zero, add_zero, Nat.cast_ofNat]
  ring

theorem correctedTransportRate_eq (δ κ : ℝ) (hδ : 0 < δ) (u v : FourierVelocity)
    (hv : Summable (fourierMoment 4 v)) (x : T3) :
    correctedTransportRate δ κ u v x =
      coordinateTransport (correctedDensity δ κ v) (InfiniteFourierTransport.velocityComponent u) x := by
  simp only [correctedTransportRate, transportVorticity, coordinateTransport,
    shiftRate_correctedDensity δ κ hδ v hv, weightedRate_eq,
    inner_add_right, real_inner_smul_right, Fin.sum_univ_three]
  ring

/-- This is exact cancellation, with no velocity supremum or frequency loss. -/
theorem integral_correctedTransportRate_zero (δ κ : ℝ) (hδ : 0 < δ)
    (u v : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hd : ∀ q, modeDot q (u q) = 0) (hv : Summable (fourierMoment 4 v)) :
    Integrable (correctedTransportRate δ κ u v) ∧
      (∫ x : T3, correctedTransportRate δ κ u v x) = 0 := by
  have h := InfiniteFourierTransport.integral_coordinateTransport_zero u hu hd
    (correctedDensity δ κ v)
    (continuous_correctedDensity δ κ hδ v (summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hv))
    (locallyLipschitz_correctedDensity δ κ hδ v (summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hv))
  simpa only [← funext (correctedTransportRate_eq δ κ hδ u v hv)] using h

end Mettapedia.FluidDynamics.NavierStokes.LocalProjectionTransport
