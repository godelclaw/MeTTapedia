import Mettapedia.Analysis.WeightedProjectionParabolic
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalCoherentStrainProduction

/-!
# Spatial diffusion balance for the weighted projection defect

The full weighted viscous rate is the ordinary Laplacian minus the
weighted Hessian, including the mixed derivative of the changing weight.
Spatial integration removes the Laplacian, not the mixed curvature.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalWeightedProjectionDiffusion

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis WeightedProjectionParabolic
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeFourierTranslationCurve PancakeHaarTransportRate
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalSpatialVorticityJets
open LocalWeightedCurlCancellation LocalVariableHelicityCenter LocalHelicityCenterParabolic
open LocalHelicityProjectionDiffusion LocalWeightedProjectionEvolution
open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open LocalCoherentStrainProduction HelicitySourceStrainSplit LocalHelicityProjectionEvolution

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def weightedFirst (δ : ℝ) (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  weightedRate δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
    (fullCurlGradient u j x) (fullCurlGradient (fourierCurl u) j x)

def weightedSecond (δ : ℝ) (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  weightedRate δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
      (fullCurlSecond u j x) (fullCurlSecond (fourierCurl u) j x) +
    weightedCurvature δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
      (fullCurlGradient u j x) (fullCurlGradient (fourierCurl u) j x)

def weightedLaplacian (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, deriv (deriv (fun h ↦ weightedProjectionDensity δ u (x + coordinateShift j h))) 0

def weightedCurvatureDensity (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, weightedCurvature δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
    (fullCurlGradient u j x) (fullCurlGradient (fourierCurl u) j x)

theorem hasDerivAt_weightedDensity_shift (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ weightedProjectionDensity δ u (x + coordinateShift j t))
      (weightedFirst δ u j (x + coordinateShift j h)) h :=
  hasDerivAt_weightedEnergy δ hδ
    (hasDerivAt_fullVorticity_shift u (summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu) j x h)
    (hasDerivAt_fullVorticity_shift (fourierCurl u) (summable_fourierMoment_curl 3 u hu) j x h)

theorem hasDerivAt_weightedFirst_shift (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ weightedFirst δ u j (x + coordinateShift j t))
      (weightedSecond δ u j (x + coordinateShift j h)) h := by
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu
  have hw3 := summable_fourierMoment_curl 3 u hu
  exact hasDerivAt_weightedRate δ hδ
    (hasDerivAt_fullVorticity_shift u hu3 j x h)
    (hasDerivAt_fullVorticity_shift (fourierCurl u) hw3 j x h)
    (hasDerivAt_fullCurlGradient_shift u hu3 j x h)
    (hasDerivAt_fullCurlGradient_shift (fourierCurl u) hw3 j x h)

theorem weightedLaplacian_eq_sum (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (x : T3) :
    weightedLaplacian δ u x = ∑ j : Fin 3, weightedSecond δ u j x := by
  apply Finset.sum_congr rfl
  intro j _
  have hd : deriv (fun h ↦ weightedProjectionDensity δ u (x + coordinateShift j h)) =
      fun h ↦ weightedFirst δ u j (x + coordinateShift j h) :=
    funext (fun h ↦ (hasDerivAt_weightedDensity_shift δ hδ u hu j x h).deriv)
  rw [hd]
  simpa only [coordinateShift_zero, add_zero] using
    (hasDerivAt_weightedFirst_shift δ hδ u hu j x 0).deriv

theorem weightedViscousRate_eq (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) (x : T3) :
    weightedViscousRate δ u x = weightedLaplacian δ u x - weightedCurvatureDensity δ u x := by
  have hu3 := summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hu
  have hw3 := summable_fourierMoment_curl 3 u hu
  rw [weightedLaplacian_eq_sum δ hδ u hu]
  unfold weightedViscousRate projectionViscousRate
  rw [← sum_fullCurlSecond u hu3 x, ← sum_fullCurlSecond (fourierCurl u) hw3 x]
  simp only [weightedSecond, weightedCurvatureDensity, weightedRate,
    RegularizedProjectionParabolic.energyRate, projectionEnergy, Fin.sum_univ_three,
    smul_add, inner_add_right, inner_sub_right, real_inner_smul_right]
  ring

theorem continuous_weightedFirst (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (j : Fin 3) :
    Continuous (weightedFirst δ u j) :=
  continuous_weightedRate δ hδ
    (continuous_fullVorticity u (summable_firstMoment_of_second u hu))
    (continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u j)
    (LocalSquaredGapGradient.continuous_fullCurlGradient (fourierCurl u) j)

theorem continuous_weightedSecond (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (j : Fin 3) :
    Continuous (weightedSecond δ u j) := by
  have ha := continuous_fullVorticity u (summable_firstMoment_of_second u hu)
  have hb := continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu)
  exact (continuous_weightedRate δ hδ ha hb
    (LocalPairedDiffusion.continuous_fullCurlSecond u j)
    (LocalPairedDiffusion.continuous_fullCurlSecond (fourierCurl u) j)).add
      (continuous_weightedCurvature δ hδ ha hb
        (LocalSquaredGapGradient.continuous_fullCurlGradient u j)
        (LocalSquaredGapGradient.continuous_fullCurlGradient (fourierCurl u) j))

theorem continuous_weightedCurvatureDensity (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    Continuous (weightedCurvatureDensity δ u) :=
  continuous_finsetSum _ (fun j _ ↦ continuous_weightedCurvature δ hδ
    (continuous_fullVorticity u (summable_firstMoment_of_second u hu))
    (continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u j)
    (LocalSquaredGapGradient.continuous_fullCurlGradient (fourierCurl u) j))

theorem integral_weightedLaplacian_eq_zero (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) :
    (∫ x : T3, weightedLaplacian δ u x) = 0 := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hi (j : Fin 3) : Integrable (weightedSecond δ u j) :=
    (continuous_weightedSecond δ hδ u hu2 j).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hz (j : Fin 3) : (∫ x : T3, weightedSecond δ u j x) = 0 :=
    UnitTorusContinuousRate.integral_rate_eq_zero (weightedFirst δ u j) (weightedSecond δ u j)
      (coordinateShift j) (continuous_weightedFirst δ hδ u hu2 j)
      (continuous_weightedSecond δ hδ u hu2 j) (continuous_coordinateShift j) (coordinateShift_zero j)
      (hasDerivAt_weightedFirst_shift δ hδ u hu j)
  simp_rw [weightedLaplacian_eq_sum δ hδ u hu]
  rw [integral_finsetSum _ (fun j _ ↦ hi j)]
  simp only [hz, Finset.sum_const_zero]

theorem integral_weightedViscousRate_eq (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) :
    (∫ x : T3, weightedViscousRate δ u x) = -(∫ x : T3, weightedCurvatureDensity δ u x) := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hiL : Integrable (weightedLaplacian δ u) := by
    have he : weightedLaplacian δ u = fun x ↦ ∑ j : Fin 3, weightedSecond δ u j x :=
      funext (weightedLaplacian_eq_sum δ hδ u hu)
    rw [he]
    exact (continuous_finsetSum _ (fun j _ ↦ continuous_weightedSecond δ hδ u hu2 j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiC : Integrable (weightedCurvatureDensity δ u) :=
    (continuous_weightedCurvatureDensity δ hδ u hu2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [weightedViscousRate_eq δ hδ u hu]
  rw [integral_sub hiL hiC, integral_weightedLaplacian_eq_zero δ hδ u hu, zero_sub]

def diffusionCostDensity (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, diffusionCost δ (fullVorticity u x) (fullVorticity (fourierCurl u) x)
    (fullCurlGradient u j x) (fullCurlGradient (fourierCurl u) j x)

/-- The coefficient derivatives are those of the actual regularized
center, not an independent field with an assumed bound. -/
theorem diffusionCostDensity_eq (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity) (x : T3) :
    diffusionCostDensity δ u x =
      42 * ‖fullVorticity u x‖ ^ 4 * projectionEnergy δ u x *
        (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) +
      2 * ‖fullVorticity u x‖ ^ 6 * (δ + ‖fullVorticity u x‖ ^ 2) *
        (∑ j : Fin 3, regularizedCenterGradient δ u j x ^ 2) := by
  simp only [diffusionCostDensity, diffusionCost, regularizedCenterGradient_eq δ hδ,
    projectionEnergy, Fin.sum_univ_three]
  ring

theorem neg_weightedCurvatureDensity_le (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity) (x : T3) :
    -weightedCurvatureDensity δ u x ≤ diffusionCostDensity δ u x := by
  unfold weightedCurvatureDensity diffusionCostDensity
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum (fun j _ ↦ neg_weightedCurvature_le δ hδ _ _ _ _)

theorem continuous_diffusionCostDensity (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    Continuous (diffusionCostDensity δ u) :=
  continuous_finsetSum _ (fun j _ ↦ continuous_diffusionCost δ hδ
    (continuous_fullVorticity u (summable_firstMoment_of_second u hu))
    (continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u j)
    (LocalSquaredGapGradient.continuous_fullCurlGradient (fourierCurl u) j))

/-- A spatial upper bound, not yet an initial-data-controlled time budget.
The weighted gradient product and the center-gradient square remain. -/
theorem integral_weightedViscousRate_le (δ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 4 u)) :
    (∫ x : T3, weightedViscousRate δ u x) ≤ ∫ x : T3, diffusionCostDensity δ u x := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4) hu
  have hiC : Integrable (fun x ↦ -weightedCurvatureDensity δ u x) :=
    (continuous_weightedCurvatureDensity δ hδ u hu2).neg.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiD : Integrable (diffusionCostDensity δ u) :=
    (continuous_diffusionCostDensity δ hδ u hu2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_weightedViscousRate_eq δ hδ u hu, ← integral_neg]
  exact integral_mono hiC hiD (neg_weightedCurvatureDensity_le δ hδ u)

/-- The scalar-reference cancellation and the full weighted diffusion
are combined on the actual material trajectory. The signed curvature,
rotation, and shifted strain all remain in the equation. -/
theorem hasDerivAt_weightedDensity_parabolic {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → Fin 3 → ℝ)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (σ : ℝ) :
    HasDerivAt (fun τ ↦ weightedProjectionDensity δ (s.coefficients τ) (torusPoint (X τ)))
      (coherentRemainder σ δ (s.coefficients t) (torusPoint (X t)) -
        2 * σ * δ * regularizedCenter δ (s.coefficients t) (torusPoint (X t)) ^ 2 *
          ‖fullVorticity (s.coefficients t) (torusPoint (X t))‖ ^ 6 +
        2 * ‖fullVorticity (s.coefficients t) (torusPoint (X t))‖ ^ 6 *
          ⟪projectionResidual δ (s.coefficients t) (torusPoint (X t)),
            rotationSource (s.coefficients t) (torusPoint (X t))⟫ +
        ν * weightedLaplacian δ (s.coefficients t) (torusPoint (X t)) -
        ν * weightedCurvatureDensity δ (s.coefficients t) (torusPoint (X t))) t := by
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  have h := hasDerivAt_weightedProjectionDensity_coherent s g hg hSum hu X hX δ hδ t ht σ
  rw [weightedViscousRate_eq δ hδ _ hm] at h
  convert h using 1
  ring

end Mettapedia.FluidDynamics.NavierStokes.LocalWeightedProjectionDiffusion
