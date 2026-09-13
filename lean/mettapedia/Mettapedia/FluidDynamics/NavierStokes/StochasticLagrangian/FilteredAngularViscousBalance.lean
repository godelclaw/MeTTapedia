import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteBandAngularDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredAngularMean
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredProjectionViscousBalance

/-!
# Actual filtered angular energy with absorbed viscous curvature

A universal normalization threshold simultaneously ensures finite-band
coercivity and pays the full viscous curvature. The remaining right-hand
side is the exact resolved inviscid work plus all-input subgrid work.
No initial-data bound for this signed source is assumed or proved here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredAngularViscousBalance

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeFrequencyProjectorCommutator
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalJointDiffusionBudget
open LocalVorticityGradientEvolution LocalAngularCurlEvolution LocalVorticityEighthMoment
open LocalHelicityCenterEvolution LocalProjectionCurvatureBudget
open FourierFiniteSupport FiniteVorticityMixedJets FiniteVorticityVariation
open FiniteAngularCurlVariation FilteredAngularMean FiniteBandAngularEnergy
open PancakeFilteredStrainDynamics InfiniteFilteredEquation PancakeLocalInfiniteVelocity
open PancakeCoefficientLimitEquation PancakePeriodicVorticityEquation

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem fullCurlGradient_viscous (P : Finset Wavevector) (ν : ℝ) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (j : Fin 3) (x : T3) :
    fullCurlGradient (unitTorusViscousVorticityCoeff ν u) j x = ν • gradientLaplacian u j x := by
  rw [← fullVorticity_derivative P _ (FilteredProjectionViscousBalance.viscous_eq_zero P ν u hs) j]
  have he : indexedDerivativeCoeff id j (unitTorusViscousVorticityCoeff ν u) =
      unitTorusViscousVorticityCoeff ν (indexedDerivativeCoeff id j u) := by
    ext q i
    simp [indexedDerivativeCoeff, unitTorusViscousVorticityCoeff]
    ring
  rw [he, FilteredProjectionViscousBalance.fullVorticity_viscous P ν _ (derivative_eq_zero P u hs j)]
  unfold fullVorticityLaplacian gradientLaplacian
  rw [spatialCurl_velocity _ (summable_fourierMoment P _ (derivative_eq_zero P u hs j) 1), fourierCurl_derivative]

theorem correctedDensityRate_viscous (P : Finset Wavevector) (ν κ : ℝ) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (x : T3) :
    FiniteAngularCurlVariation.correctedDensityRate κ u (unitTorusViscousVorticityCoeff ν u) x =
      FiniteBandAngularDiffusion.correctedViscousDensity ν κ u x := by
  unfold FiniteAngularCurlVariation.correctedDensityRate FiniteAngularCurlVariation.densityRate
  rw [FilteredProjectionViscousBalance.fullVorticity_viscous P ν u hs x]
  have he : (fun j ↦ fullCurlGradient (unitTorusViscousVorticityCoeff ν u) j x) =
      fun j ↦ ν • gradientLaplacian u j x := funext (fun j ↦ fullCurlGradient_viscous P ν u hs j x)
  rw [he, AngularCurlDecomposition.angularCurlDensityRate_smul]
  simp only [FiniteBandAngularDiffusion.correctedViscousDensity, octicViscousDensity,
    viscousDensityRate, real_inner_smul_right]
  ring

def work (κ : ℝ) (P : Finset Wavevector) (u v : FourierVelocity) : ℝ :=
  meanWork κ u (restrictVelocity P v)

theorem work_add (κ : ℝ) (P : Finset Wavevector) (u v w : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    work κ P u (v + w) = work κ P u v + work κ P u w :=
  meanWork_restrict_add κ P u v w hs

theorem work_viscous (P : Finset Wavevector) (ν κ : ℝ) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    work κ P u (unitTorusViscousVorticityCoeff ν u) =
      ∫ x : T3, FiniteBandAngularDiffusion.correctedViscousDensity ν κ u x := by
  unfold work meanWork
  rw [FilteredProjectionMean.restrictVelocity_eq_self P _
    (FilteredProjectionViscousBalance.viscous_eq_zero P ν u hs)]
  simp_rw [correctedDensityRate_viscous P ν κ u hs]

theorem hasDerivAt_correctedEnergy_viscous {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B) (κ : ℝ)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ correctedEnergy κ (filteredVelocity χ (s.coefficients τ)))
      (work κ P (filteredVelocity χ (s.coefficients t))
          (infiniteVelocityRHS 0 (filteredVelocity χ (s.coefficients t))) +
        work κ P (filteredVelocity χ (s.coefficients t)) (subgridForce χ (s.coefficients t)) +
        ∫ x : T3, FiniteBandAngularDiffusion.correctedViscousDensity ν κ
          (filteredVelocity χ (s.coefficients t)) x) t := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ (s.coefficients t) q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have h := hasDerivAt_correctedEnergy_split s hB κ P χ hcut C hχ t ht
  change HasDerivAt _ (work κ P _ (infiniteVelocityRHS ν _) + work κ P _ _) t at h
  rw [infiniteVelocityRHS_eq_zero_add_viscous, work_add κ P _ _ _ hs, work_viscous P ν κ _ hs] at h
  apply h.congr_deriv
  ring

/-- The same universal radius-squared threshold gives both coercivity
and a dissipative differential inequality for the actual filtered solution. -/
theorem exists_coercive_dissipative_threshold :
    ∃ L : ℝ, 0 < L ∧ ∀ {ν T B : ℝ} {u₀ : FourierVelocity}
      (s : LocalInfiniteVelocitySolution ν u₀ T B), 0 ≤ ν → 0 ≤ B →
      ∀ (κ : ℝ), 0 < κ → ∀ (P : Finset Wavevector) (χ : Wavevector → ℂ),
      (∀ q, q ∉ P → χ q = 0) → ∀ C : ℝ, (∀ q, ‖χ q‖ ≤ C) →
      ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) → L * (2 * Real.pi * R) ^ 2 ≤ κ →
      ∀ t ∈ Set.Ioo (0 : ℝ) T,
      (meanEnergy (filteredVelocity χ (s.coefficients t)) / 16 ≤
          correctedEnergy κ (filteredVelocity χ (s.coefficients t)) ∧
        correctedEnergy κ (filteredVelocity χ (s.coefficients t)) ≤
          meanEnergy (filteredVelocity χ (s.coefficients t)) / 8) ∧
      deriv (fun τ ↦ correctedEnergy κ (filteredVelocity χ (s.coefficients τ))) t +
          (ν / 2) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) +
          6 * ν * radialDissipation (filteredVelocity χ (s.coefficients t)) ≤
        work κ P (filteredVelocity χ (s.coefficients t))
            (infiniteVelocityRHS 0 (filteredVelocity χ (s.coefficients t))) +
          work κ P (filteredVelocity χ (s.coefficients t)) (subgridForce χ (s.coefficients t)) := by
  obtain ⟨D, hD, hdiff⟩ := FiniteBandAngularDiffusion.exists_diffusion_threshold
  refine ⟨6 * D + 768, by positivity, fun s hν hB κ hκ P χ hcut C hχ R hP hscale t ht ↦ ?_⟩
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ (s.coefficients t) q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hp : 0 ≤ (2 * Real.pi * R) ^ 2 := sq_nonneg _
  have hsmall : 6 * D * (2 * Real.pi * R) ^ 2 ≤ κ := by nlinarith only [hscale, hp]
  have hlarge : 48 * (8 * Real.pi * R) ^ 2 ≤ κ := by
    nlinarith only [hscale, mul_nonneg hD.le hp]
  refine ⟨correctedEnergy_bounds P _ hs R hP κ hκ hlarge, ?_⟩
  rw [(hasDerivAt_correctedEnergy_viscous s hB κ P χ hcut C hχ t ht).deriv]
  have h := hdiff P _ hs R hP _ κ hν hκ hsmall
  linarith only [h]

end Mettapedia.FluidDynamics.NavierStokes.FilteredAngularViscousBalance
