import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalProjectionCurvatureBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredProjectionMean

/-!
# Viscous separation in the actual filtered projection-energy balance

The finite filter is applied to a genuine infinite solution, not evolved
by a closed Galerkin equation. Resolved inviscid work and all-input subgrid
work remain signed. The viscosity contribution is the ordinary spatial
Laplacian and has an explicit upper bound by weighted derivative costs.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredProjectionViscousBalance

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge
open PancakeDyadicDirectionEvolution PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian
open PancakeIncomingLowSourceEnergy PancakeFourierMaterialPaths PancakeTransverseEnergyFreezing
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentForcing
open LocalWeightedProjectionEvolution LocalHelicityProjectionEvolution LocalHelicityProjectionDiffusion
open LocalProjectionCurvatureBudget LocalWeightedProjectionDiffusion
open LocalVorticityEighthMoment LocalProjectionSourceWork LocalHelicityCenterEvolution
open FourierFiniteSupport FiniteVorticityVariation FilteredProjectionMean
open PancakeFilteredStrainDynamics InfiniteFilteredEquation PancakeLocalInfiniteVelocity
open PancakeCoefficientLimitEquation
open PancakePeriodicVorticityEquation

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem viscous_eq_zero (P : Finset Wavevector) (ν : ℝ) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (q : Wavevector) (hq : q ∉ P) :
    unitTorusViscousVorticityCoeff ν u q = 0 := by
  simp [unitTorusViscousVorticityCoeff, hs q hq]

theorem fullVorticity_viscous (P : Finset Wavevector) (ν : ℝ) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (x : T3) :
    fullVorticity (unitTorusViscousVorticityCoeff ν u) x = ν • fullVorticityLaplacian u x := by
  have hu1 := summable_fourierMoment P u hs 1
  have hv1 := summable_fourierMoment P _ (viscous_eq_zero P ν u hs) 1
  have hw2 := summable_fourierMoment P _ (fourierCurl_eq_zero P u hs) 2
  unfold fullVorticity fullVorticityLaplacian
  rw [spatialCurl_velocity _ hv1, funext (curl_viscous u ν),
    fullFourierField_viscous ν _ hw2 x, spatialCurl_velocity u hu1]
  ext i
  simp [complexRealPartEuclideanCLM_apply, complexRealPartEuclidean]

theorem correctedDensityRate_viscous (P : Finset Wavevector) (ν δ κ : ℝ) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (x : T3) :
    correctedDensityRate δ κ u (unitTorusViscousVorticityCoeff ν u) x =
      correctedViscousDensity ν δ κ u x := by
  unfold correctedDensityRate densityRate
  rw [fullVorticity_viscous P ν u hs x, funext (curl_viscous u ν),
    fullVorticity_viscous P ν (fourierCurl u) (fourierCurl_eq_zero P u hs) x,
    WeightedProjectionVariation.weightedRate_smul]
  simp only [correctedViscousDensity, octicViscousDensity, weightedViscousRate,
    WeightedProjectionParabolic.weightedRate, RegularizedProjectionParabolic.energyRate,
    projectionEnergy, projectionViscousRate, real_inner_smul_right]
  ring

def work (δ κ : ℝ) (P : Finset Wavevector) (u v : FourierVelocity) : ℝ :=
  ∫ x : T3, ⟪correctedGradient δ κ u x, fullVorticity (restrictVelocity P v) x⟫

theorem integrable_workDensity (δ κ : ℝ) (hδ : 0 < δ) (P : Finset Wavevector)
    (u v : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    Integrable (fun x : T3 ↦ ⟪correctedGradient δ κ u x, fullVorticity (restrictVelocity P v) x⟫) := by
  have hω := LocalLowDiffusionBudget.continuous_fullVorticity u (summable_firstMoment_of_second u hu)
  have hG : Continuous (correctedGradient δ κ u) :=
    ((hω.norm.pow 6).smul hω).sub ((continuous_projectionGradient δ hδ u hu).const_smul _)
  exact (hG.inner (LocalLowDiffusionBudget.continuous_fullVorticity _
    (summable_fourierMoment P _ (restrictVelocity_eq_zero P v) 1))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem work_add (δ κ : ℝ) (hδ : 0 < δ) (P : Finset Wavevector)
    (u v w : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    work δ κ P u (v + w) = work δ κ P u v + work δ κ P u w := by
  unfold work
  simp_rw [fullVorticity_restrictVelocity, spatialVorticity_add, inner_add_right]
  have hv := integrable_workDensity δ κ hδ P u v hu
  have hw := integrable_workDensity δ κ hδ P u w hu
  simp only [fullVorticity_restrictVelocity] at hv hw
  exact integral_add hv hw

theorem work_viscous (P : Finset Wavevector) (ν δ κ : ℝ) (hδ : 0 < δ)
    (u : FourierVelocity) (hs : ∀ q, q ∉ P → u q = 0) :
    work δ κ P u (unitTorusViscousVorticityCoeff ν u) =
      -ν * weightedPalinstrophy u - 6 * ν * radialDissipation u +
        (3 * ν / κ) * (∫ x : T3, weightedCurvatureDensity δ u x) := by
  have hu4 := summable_fourierMoment P u hs 4
  have hv3 := summable_fourierMoment P _ (viscous_eq_zero P ν u hs) 3
  unfold work
  rw [restrictVelocity_eq_self P _ (viscous_eq_zero P ν u hs),
    ← integral_correctedDensityRate_eq δ hδ κ _ _ hu4 hv3]
  simp_rw [correctedDensityRate_viscous P ν δ κ u hs]
  exact integral_correctedViscousDensity_eq ν δ κ hδ u hu4

/-- The two signed work terms contain the resolved nonlinearity and the
complete unresolved-input source. Neither is bounded in this identity. -/
theorem hasDerivAt_meanCorrectedEnergy_viscous {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B)
    (δ : ℝ) (hδ : 0 < δ) (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ meanCorrectedEnergy δ κ (filteredVelocity χ (s.coefficients τ)))
      (work δ κ P (filteredVelocity χ (s.coefficients t))
          (infiniteVelocityRHS 0 (filteredVelocity χ (s.coefficients t))) +
        work δ κ P (filteredVelocity χ (s.coefficients t)) (subgridForce χ (s.coefficients t)) -
        ν * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) -
        6 * ν * radialDissipation (filteredVelocity χ (s.coefficients t)) +
        (3 * ν / κ) * (∫ x : T3, weightedCurvatureDensity δ (filteredVelocity χ (s.coefficients t)) x)) t := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ (s.coefficients t) q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have h := hasDerivAt_meanCorrectedEnergy_split s hB δ hδ κ P χ hcut C hχ t ht
  change HasDerivAt _ (work δ κ P _ (infiniteVelocityRHS ν _) + work δ κ P _ _) t at h
  rw [infiniteVelocityRHS_eq_zero_add_viscous, work_add δ κ hδ P _ _ _
    (summable_fourierMoment P _ hs 2), work_viscous P ν δ κ hδ _ hs] at h
  apply h.congr_deriv
  ring

theorem deriv_meanCorrectedEnergy_le {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 ≤ ν) (hB : 0 ≤ B)
    (δ : ℝ) (hδ : 0 < δ) (κ : ℝ) (hκ : 0 < κ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    deriv (fun τ ↦ meanCorrectedEnergy δ κ (filteredVelocity χ (s.coefficients τ))) t ≤
      work δ κ P (filteredVelocity χ (s.coefficients t))
          (infiniteVelocityRHS 0 (filteredVelocity χ (s.coefficients t))) +
        work δ κ P (filteredVelocity χ (s.coefficients t)) (subgridForce χ (s.coefficients t)) -
        ν * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) -
        6 * ν * radialDissipation (filteredVelocity χ (s.coefficients t)) +
        (3 * ν / κ) * curvatureCost (filteredVelocity χ (s.coefficients t)) := by
  rw [(hasDerivAt_meanCorrectedEnergy_viscous s hB δ hδ κ P χ hcut C hχ t ht).deriv]
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ (s.coefficients t) q = 0 := by
    simp [filteredVelocity, hcut q hq]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (integral_weightedCurvatureDensity_le δ hδ _ (summable_fourierMoment P _ hs 2))
      (show 0 ≤ 3 * ν / κ by positivity))

end Mettapedia.FluidDynamics.NavierStokes.FilteredProjectionViscousBalance
