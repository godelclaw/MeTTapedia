import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteLowStrainWork
import Mettapedia.Analysis.ODE.SignedEnergyBalance

/-!
# Signed angular balance after initial-energy low-strain payment

The low-strain growth rate is fixed by the initial kinetic energy and a
fixed source cutoff, independently of the retained frequencies. An
integrating factor removes this rate while retaining the sign of the
joint residual strain and full subgrid work. No bound on that residual
is assumed or proved here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LowStrainAngularBalance

open scoped RealInnerProductSpace ComplexConjugate Matrix.Norms.Elementwise
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeInfiniteFourierDerivative PancakePeriodicVorticityEquation PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeMeasurableMaterialRate
open PancakeTransverseEnergyFreezing PancakeDyadicDirectionEvolution
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticityEighthMoment
open FourierFiniteSupport FiniteVorticityMixedJets FiniteAngularSourceWork
open FiniteLowStrainWork FiniteBandAngularEnergy FiniteAngularCurlVariation
open FilteredAngularStrainIntegral AngularTransportAbsorption FiniteVelocityGradientEnergy
open PancakeLocalInfiniteVelocity LocalKineticEnergy InfiniteConvectionEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuous_correctedGradient_parametric {Y : Type*} [TopologicalSpace Y]
    (κ : ℝ) (P : Finset Wavevector) (u : Y → FourierVelocity)
    (hs : ∀ y q, q ∉ P → u y q = 0)
    (hu : ∀ q ∈ P, ∀ i, Continuous (fun y ↦ u y q i)) :
    Continuous (fun z : Y × T3 ↦ correctedGradient κ (u z.1) z.2) := by
  have ha := FilteredProjectionMean.continuous_fullVorticity P u hs hu
  have hD := FiniteAngularCurlVariation.continuous_fullCurlGradient P u hs hu
  have hm (j k : Fin 3) : Continuous (fun z : Y × T3 ↦ mixed (u z.1) j k z.2) := by
    have h := FiniteAngularCurlVariation.continuous_fullCurlGradient P
      (fun y ↦ indexedDerivativeCoeff id j (u y))
      (fun y ↦ derivative_eq_zero P _ (hs y) j)
      (fun q hq i ↦ (hu q hq i).const_mul (unitTorusDerivativePhase * (q j : ℂ))) k
    simpa only [fullCurlGradient, fourierCurl_derivative, mixed, InfiniteFourierDiffusion.mappedField] using h
  have hA := AngularCurlDecomposition.continuous_variationalGradient _ _ _ ha hD (fun j k ↦ hm k j)
  exact ((ha.norm.pow 6).smul ha).sub (hA.const_smul (3 / κ))

theorem continuousOn_lowStrainWork {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (κ : ℝ) (P Q : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0) :
    ContinuousOn (fun t ↦ lowStrainWork κ Q (s.coefficients t)
      (filteredVelocity χ (s.coefficients t))) (Set.Icc (0 : ℝ) T) := by
  have hs (t : Set.Icc (0 : ℝ) T) (q : Wavevector) (hq : q ∉ P) :
      filteredVelocity χ (s.coefficients t) q = 0 := by simp [filteredVelocity, hcut q hq]
  have hc (q : Wavevector) (i : Fin 3) :
      Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q i) :=
    (s.continuous q i).comp continuous_subtype_val
  have hχc (q : Wavevector) (_hq : q ∈ P) (i : Fin 3) :
      Continuous (fun t : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients t) q i) :=
    continuous_const.mul (hc q i)
  have hF := continuous_correctedGradient_parametric κ P _ hs hχc
  have ha := FilteredProjectionMean.continuous_fullVorticity P _ hs hχc
  have hS := continuous_subtype_val.comp
    (continuous_parametric_strain Q (fun _ ↦ 1)
      (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t) (fun q _ i ↦ hc q i))
  have he (v : FourierVelocity) : filteredVelocity (fun _ ↦ 1) v = v := by
    funext q
    exact one_smul ℂ (v q)
  simp only [he] at hS
  exact LocalAlignmentContinuity.continuousOn_spatialIntegral
    (fun t x ↦ ⟪correctedGradient κ (filteredVelocity χ (s.coefficients t)) x,
      lowStrainSource Q (s.coefficients t) (filteredVelocity χ (s.coefficients t)) x⟫)
    (hF.inner (hS.clm_apply ha))

theorem continuousOn_residualStrainSubgridWork {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B) (κ : ℝ)
    (P Q : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q)) :
    ContinuousOn (fun t ↦ residualStrainSubgridWork κ Q χ (s.coefficients t)) (Set.Icc (0 : ℝ) T) := by
  apply ((continuousOn_strainSubgridWork s hB κ P χ hcut C hχ hχr).sub
    (continuousOn_lowStrainWork s κ P Q χ hcut)).congr
  intro t _
  have h := strainSubgridWork_eq_low_add_residual κ P Q χ hcut (s.coefficients t)
  linarith only [h]

/-- The coefficient of corrected energy is independent of the retained
cutoff. The complete residual is still signed and unpaid. -/
theorem exists_residual_differential_inequality :
    ∃ L : ℝ, 0 < L ∧ ∀ {ν T B : ℝ} {u₀ : FourierVelocity}
      (s : LocalInfiniteVelocitySolution ν u₀ T B), 0 ≤ ν → 0 ≤ B →
      ∀ (g : Wavevector → ℝ), (∀ q, 0 ≤ g q) → Summable g →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q) →
      ∀ (κ : ℝ), 0 < κ → ∀ (P Q : Finset Wavevector) (χ : Wavevector → ℂ),
      (∀ q, q ∉ P → χ q = 0) → ∀ C : ℝ, (∀ q, ‖χ q‖ ≤ C) →
      (∀ q, χ (-q) = conj (χ q)) →
      ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) → 1 + L * (2 * Real.pi * R) ^ 2 ≤ κ →
      432 * Real.sqrt (derivativeCutoffWeight P χ * kineticEnergy u₀) ≤ ν * κ →
      ∀ t ∈ Set.Ioo (0 : ℝ) T,
      deriv (fun τ ↦ correctedEnergy κ (filteredVelocity χ (s.coefficients τ))) t +
          (ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) +
          6 * ν * radialDissipation (filteredVelocity χ (s.coefficients t)) ≤
        (16 * lowStrainGrowthCoefficient Q (kineticEnergy u₀)) *
          correctedEnergy κ (filteredVelocity χ (s.coefficients t)) +
            residualStrainSubgridWork κ Q χ (s.coefficients t) := by
  obtain ⟨L, hL, hbound⟩ := exists_coercive_strain_subgrid_threshold
  refine ⟨L + 16, by positivity, ?_⟩
  intro ν T B u₀ s hν hB g hg hSum hu κ hκ P Q χ hcut C hχ hχr R hP hscale hpay t ht
  have hp := sq_nonneg (2 * Real.pi * R)
  have hscale₁ : L * (2 * Real.pi * R) ^ 2 ≤ κ := by nlinarith only [hscale, hp]
  have hscale₂ : 1 + (8 * Real.pi * R) ^ 2 ≤ κ := by
    nlinarith only [hscale, mul_nonneg hL.le hp]
  have h := hbound s hν hB g hg hSum hu κ hκ P χ hcut C hχ hχr R hP hscale₁ hpay t ht
  have hb := abs_lowStrainWork_solution_le s hν g hg hSum hu P Q χ hcut κ R hκ hP hscale₂ t
    (Set.Ioo_subset_Icc_self ht)
  have he := strainSubgridWork_eq_low_add_residual κ P Q χ hcut (s.coefficients t)
  have hc := mul_le_mul_of_nonneg_left h.1.1 (lowStrainGrowthCoefficient_nonneg Q (kineticEnergy u₀))
  have hl := le_abs_self (lowStrainWork κ Q (s.coefficients t) (filteredVelocity χ (s.coefficients t)))
  have hbnd := h.2
  change _ ≤ strainSubgridWork κ χ (s.coefficients t) at hbnd
  nlinarith only [hbnd, hb, he, hc, hl]

end Mettapedia.FluidDynamics.NavierStokes.LowStrainAngularBalance
