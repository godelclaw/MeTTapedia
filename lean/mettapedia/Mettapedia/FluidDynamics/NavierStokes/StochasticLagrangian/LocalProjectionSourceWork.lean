import Mettapedia.Analysis.UnitTorusProjectionVariation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteVorticityVariation

/-!
# Signed source work of the actual projection correction

Curl integration by parts removes the extra derivative of an additional
vorticity source. The variational gradient is constructed from the actual
field and its ordinary spatial jets; its size remains to be estimated.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalProjectionSourceWork

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis WeightedProjectionParabolic UnitTorusProjectionVariation
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy LocalLowDiffusionBudget LocalSpatialVorticityJets
open LocalAlignmentForcing LocalJointDiffusionBudget LocalWeightedCurlCancellation
open FiniteVorticityVariation
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def projectionGradient (δ : ℝ) (u : FourierVelocity) (x : T3) : R3 :=
  variationalGradient δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
    (fun j ↦ fullCurlGradient u j x) (fun j ↦ fullCurlGradient (fourierCurl u) j x)

theorem continuous_projectionGradient (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) : Continuous (projectionGradient δ u) :=
  continuous_variationalGradient δ hδ
    (continuous_fullVorticity u (summable_firstMoment_of_second u hu))
    (continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u)
    (LocalSquaredGapGradient.continuous_fullCurlGradient (fourierCurl u))

theorem integral_densityRate_eq (δ : ℝ) (hδ : 0 < δ) (u v : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hv : Summable (fourierMoment 3 v)) :
    (∫ x : T3, densityRate δ u v x) =
      ∫ x : T3, ⟪projectionGradient δ u x, fullVorticity v x⟫ := by
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hv2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hv
  have hw3 := summable_fourierMoment_curl 3 u hu
  have hi := integral_weightedRate_eq δ hδ
    (fullVorticity u) (fullVorticity (fourierCurl u)) (fullVorticity v)
    (fullCurlGradient u) (fullCurlGradient (fourierCurl u)) (fullCurlGradient v)
    (continuous_fullVorticity u (summable_firstMoment_of_second u hu2))
    (continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu2))
    (continuous_fullVorticity v (summable_firstMoment_of_second v hv2))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u)
    (LocalSquaredGapGradient.continuous_fullCurlGradient (fourierCurl u))
    (LocalSquaredGapGradient.continuous_fullCurlGradient v)
    (hasDerivAt_fullVorticity_shift u hu3) (hasDerivAt_fullVorticity_shift (fourierCurl u) hw3)
    (hasDerivAt_fullVorticity_shift v hv)
  simpa only [densityRate, projectionGradient, ← fullVorticity_curl_eq_curlJet v hv2] using hi

def correctedGradient (δ κ : ℝ) (u : FourierVelocity) (x : T3) : R3 :=
  ‖fullVorticity u x‖ ^ 6 • fullVorticity u x - (3 / κ) • projectionGradient δ u x

theorem integral_correctedDensityRate_eq (δ : ℝ) (hδ : 0 < δ) (κ : ℝ) (u v : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hv : Summable (fourierMoment 3 v)) :
    (∫ x : T3, correctedDensityRate δ κ u v x) =
      ∫ x : T3, ⟪correctedGradient δ κ u x, fullVorticity v x⟫ := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hv2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hv
  have ha := continuous_fullVorticity u (summable_firstMoment_of_second u hu2)
  have hb := continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu2)
  have hf := continuous_fullVorticity v (summable_firstMoment_of_second v hv2)
  have hg := continuous_fullVorticity (fourierCurl v) (summable_fourierMoment_curl 1 v hv2)
  have hA : Integrable (fun x ↦ ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x, fullVorticity v x⟫) :=
    ((ha.norm.pow 6).mul (ha.inner hf)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hK : Integrable (densityRate δ u v) :=
    (continuous_weightedRate δ hδ ha hb hf hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP : Integrable (fun x ↦ ⟪projectionGradient δ u x, fullVorticity v x⟫) :=
    ((continuous_projectionGradient δ hδ u hu2).inner hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [correctedDensityRate, correctedGradient, inner_sub_left, real_inner_smul_left]
  rw [integral_sub hA (hK.const_mul _), integral_sub hA (hP.const_mul _),
    integral_const_mul, integral_const_mul, integral_densityRate_eq δ hδ u v hu hv]

end Mettapedia.FluidDynamics.NavierStokes.LocalProjectionSourceWork
