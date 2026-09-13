import Mettapedia.Analysis.WeightedProjectionCurvatureBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedProjectionDiffusion

/-!
# Correct-sign viscous bound for a subtracted projection energy

The spatial curvature upper bound has no inverse regularization or
moving-center gradient. It leaves an explicit weighted derivative cost.
No estimate by the octic dissipation, uniform in a frequency cutoff, is
assumed here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalProjectionCurvatureBudget

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeHigherDerivativeMoments LocalLowDiffusionBudget LocalJointDiffusionBudget
open LocalSpatialVorticityJets LocalWeightedProjectionDiffusion LocalWeightedProjectionEvolution
open LocalVorticityEighthMoment GaussianRootWeightedIncrement
open LocalAlignmentForcing LocalWeightedCurlCancellation

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def curvatureCostDensity (u : FourierVelocity) (x : T3) : ℝ :=
  70 * ‖fullVorticity u x‖ ^ 4 * ‖fullVorticity (fourierCurl u) x‖ ^ 2 *
    (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) +
  28 * ‖fullVorticity u x‖ ^ 6 *
    (∑ j : Fin 3, ‖fullCurlGradient (fourierCurl u) j x‖ ^ 2)

def curvatureCost (u : FourierVelocity) : ℝ := ∫ x : T3, curvatureCostDensity u x

theorem curvatureCostDensity_nonneg (u : FourierVelocity) (x : T3) :
    0 ≤ curvatureCostDensity u x := by unfold curvatureCostDensity; positivity

theorem curvatureCost_nonneg (u : FourierVelocity) : 0 ≤ curvatureCost u :=
  integral_nonneg (curvatureCostDensity_nonneg u)

theorem weightedCurvatureDensity_le (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity) (x : T3) :
    weightedCurvatureDensity δ u x ≤ curvatureCostDensity u x := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
    WeightedProjectionCurvatureBound.weightedCurvature_le δ hδ (fullVorticity u x)
      (fullVorticity (fourierCurl u) x) (fullCurlGradient u j x)
      (fullCurlGradient (fourierCurl u) j x))
  simpa only [weightedCurvatureDensity, curvatureCostDensity, Finset.sum_add_distrib,
    ← Finset.mul_sum] using h

theorem continuous_curvatureCostDensity (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) : Continuous (curvatureCostDensity u) := by
  have ha := continuous_fullVorticity u (summable_firstMoment_of_second u hu)
  have hb := continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu)
  have hD (v : FourierVelocity) : Continuous (fun x : T3 ↦ ∑ j : Fin 3, ‖fullCurlGradient v j x‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ ↦ (LocalSquaredGapGradient.continuous_fullCurlGradient v j).norm.pow 2)
  exact ((((ha.norm.pow 4).const_mul 70).mul (hb.norm.pow 2)).mul (hD u)).add
    (((ha.norm.pow 6).const_mul 28).mul (hD (fourierCurl u)))

theorem integral_weightedCurvatureDensity_le (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    (∫ x : T3, weightedCurvatureDensity δ u x) ≤ curvatureCost u :=
  integral_mono
    ((continuous_weightedCurvatureDensity δ hδ u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((continuous_curvatureCostDensity u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (weightedCurvatureDensity_le δ hδ u)

def octicViscousDensity (u : FourierVelocity) (x : T3) : ℝ :=
  ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x, fullVorticityLaplacian u x⟫

theorem octicViscousDensity_eq (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (x : T3) :
    octicViscousDensity u x = energyLaplacian u x / 8 -
      weightedPalinstrophyDensity u x - 6 * radialGradientDensity u x := by
  rw [energyLaplacian_eq u hu x]
  unfold octicViscousDensity
  ring

theorem integrable_octicViscousDensity (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    Integrable (octicViscousDensity u) := by
  have hG : Integrable (weightedPalinstrophyDensity u) := (continuous_weightedPalinstrophyDensity u hu).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (radialGradientDensity u) := (continuous_radialGradientDensity u hu).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  change Integrable (fun x : T3 ↦ octicViscousDensity u x)
  simp_rw [octicViscousDensity_eq u hu]
  exact (((integrable_energyLaplacian_and_integral_zero u hu).1.div_const 8).sub hG).sub (hR.const_mul 6)

theorem integral_octicViscousDensity (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T3, octicViscousDensity u x) = -weightedPalinstrophy u - 6 * radialDissipation u := by
  have hG : Integrable (weightedPalinstrophyDensity u) :=
    (continuous_weightedPalinstrophyDensity u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (radialGradientDensity u) :=
    (continuous_radialGradientDensity u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨hL, hz⟩ := integrable_energyLaplacian_and_integral_zero u hu
  simp_rw [octicViscousDensity_eq u hu]
  have h1 := integral_sub ((hL.div_const 8).sub hG) (hR.const_mul 6)
  have h2 := integral_sub (hL.div_const 8) hG
  simp only [Pi.sub_apply] at h1 h2
  rw [h1, h2, integral_div, integral_const_mul, hz]
  simp only [zero_div, zero_sub, weightedPalinstrophy, radialDissipation]

def correctedViscousDensity (ν δ κ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ν * octicViscousDensity u x - (3 * ν / κ) * weightedViscousRate δ u x

theorem integrable_weightedViscousRate (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) :
    Integrable (weightedViscousRate δ u) := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hL : Integrable (fun x : T3 ↦ ∑ j : Fin 3, weightedSecond δ u j x) :=
    (continuous_finsetSum _ (fun j _ ↦ continuous_weightedSecond δ hδ u hu2 j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hC : Integrable (weightedCurvatureDensity δ u) := (continuous_weightedCurvatureDensity δ hδ u hu2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  change Integrable (fun x : T3 ↦ weightedViscousRate δ u x)
  simp_rw [weightedViscousRate_eq δ hδ u hu, weightedLaplacian_eq_sum δ hδ u hu]
  exact hL.sub hC

/-- The positive sign on the curvature integral is essential. -/
theorem integral_correctedViscousDensity_eq (ν δ κ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) :
    (∫ x : T3, correctedViscousDensity ν δ κ u x) =
      -ν * weightedPalinstrophy u - 6 * ν * radialDissipation u +
        (3 * ν / κ) * (∫ x : T3, weightedCurvatureDensity δ u x) := by
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu
  unfold correctedViscousDensity
  rw [integral_sub ((integrable_octicViscousDensity u hu3).const_mul ν)
    ((integrable_weightedViscousRate δ hδ u hu).const_mul (3 * ν / κ))]
  simp only [integral_const_mul, integral_octicViscousDensity u hu3,
    integral_weightedViscousRate_eq δ hδ u hu]
  ring

theorem integral_correctedViscousDensity_le (ν δ κ : ℝ) (hν : 0 ≤ ν) (hδ : 0 < δ) (hκ : 0 < κ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) :
    (∫ x : T3, correctedViscousDensity ν δ κ u x) ≤
      -ν * weightedPalinstrophy u - 6 * ν * radialDissipation u + (3 * ν / κ) * curvatureCost u := by
  rw [integral_correctedViscousDensity_eq ν δ κ hδ u hu]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (integral_weightedCurvatureDensity_le δ hδ u
      (summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu))
        (show 0 ≤ 3 * ν / κ by positivity))

end Mettapedia.FluidDynamics.NavierStokes.LocalProjectionCurvatureBudget
