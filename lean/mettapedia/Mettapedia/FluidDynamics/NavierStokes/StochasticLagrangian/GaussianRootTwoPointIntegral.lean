import Mettapedia.Analysis.RootPartitionTwoPointIntegrability
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootTwoPointDerivative
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentRelativeMoment

/-!
# Integrating the actual Gaussian two-point derivative cost

The gap-factor and projector coordinate derivatives have finite spatial
square integrals. Continuous two-point coefficients preserve integrability
after both kernel translations. Compactness is used for integrability only;
the actual coefficients and derivative costs remain in the final integral.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointIntegral

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierTranslationCurve
open LocalLowDiffusionBudget LocalSquaredGapPressure LocalSpatialVorticityJets
open PancakeHigherDerivativeMoments GaussianRootVorticity GaussianRootTwoPointDerivative
open GaussianRootWeakChannelBudget
open Mettapedia.Analysis.EuclideanOperatorCoordinates
open Mettapedia.Analysis.GaussianPartitionEnergy Mettapedia.Analysis.BilinearTranslatedCoefficient

local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "X3" => Fin 3 → ℝ
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem twoPointBudget_nonneg (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (j : Fin 3) (y z : T3) :
    0 ≤ twoPointBudget gamma chi modes u centers tau j y z := by
  letI : Nonempty ↑centers := ⟨⟨hc.choose, hc.choose_spec⟩⟩
  have hH := twoPointDistanceMoment_nonneg
    (fun i : ↑centers ↦ coordinates (localProjector gamma chi modes u i.1)) tau
    (coordinates (localProjector gamma chi modes u y)) (coordinates (localProjector gamma chi modes u z))
  dsimp only [twoPointBudget]
  positivity

theorem integrable_rootGapDerivative_sq (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (j : Fin 3) :
    Integrable (fun y : T3 ↦ deriv (fun h ↦
      rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) (y + coordinateShift j h))) 0 ^ 2) := by
  have hS := PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u)
  have hlS : LocallyLipschitz
      (fun r : X3 ↦ spatialStrain modes (filteredVelocity chi u) (torusPoint r)) :=
    fun r ↦ (LocalSpatialBottomProjector.contDiff_spatialStrain (n := 1) chi modes u).locallyLipschitz r
  exact (PeriodicFourierGradientEnergy.memLp_coordinateRate
    (fun x ↦ rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) x)) j
    ((locallyLipschitz_rootGapFactor gamma hg).continuous.comp hS)
    ((locallyLipschitz_rootGapFactor gamma hg).comp hlS)).integrable_sq

theorem integrable_projectorCoordinateDerivative_sq (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) :
    Integrable (fun y : T3 ↦
      ‖coordinates (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j y)‖ ^ 2) := by
  have hs := LocalSquaredGapGradient.stronglyMeasurable_coordinateDerivative gamma hg chi modes u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu) j
  have hi : Integrable (fun y : T3 ↦
      ‖LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j y‖ ^ 2) := by
    apply (LocalSquaredGapGradient.integrable_gradientSquare gamma hg chi modes u hu).mono'
      (hs.norm.pow 2).aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j y‖ ^ 2 ≤
      ∑ k : Fin 3, ‖LocalSquaredGapGradient.coordinateDerivative gamma chi modes u k y‖ ^ 2
    exact Finset.single_le_sum
      (f := fun k : Fin 3 ↦ ‖LocalSquaredGapGradient.coordinateDerivative gamma chi modes u k y‖ ^ 2)
      (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j)
  have hLp := (memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mpr hi
  exact ((coordinates (ι := Fin 3)).comp_memLp' hLp).norm.integrable_sq

theorem integrable_twoPointBudget (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (j : Fin 3) (M : T6 → ℝ) (hM : Integrable M)
    (a b : T6 → T3) (ha : Measurable a) (hb : Measurable b) :
    Integrable (fun p : T6 × T3 ↦ M p.1 *
      twoPointBudget gamma chi modes u centers tau j (p.2 - a p.1) (p.2 - b p.1))
      ((volume : Measure T6).prod (volume : Measure T3)) := by
  letI : Nonempty ↑centers := ⟨⟨hc.choose, hc.choose_spec⟩⟩
  let B := fun x : T3 ↦ rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) x)
  let P := fun x : T3 ↦ coordinates (localProjector gamma chi modes u x)
  let w := fun x : T3 ↦ ‖fullVorticity u x‖
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hB : Continuous B := (locallyLipschitz_rootGapFactor gamma hg).continuous.comp
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
  have hP : Continuous P := (coordinates (ι := Fin 3)).continuous.comp
    (continuous_localProjector gamma hg chi modes u hu1)
  have hw : Continuous w := (continuous_fullVorticity u hu1).norm
  have h := Mettapedia.Analysis.RootPartitionEnergy.integrable_twoPointDerivativeCost B w P
    (fun y ↦ deriv (fun h ↦ B (y + coordinateShift j h)) 0)
    (fun y ↦ ‖coordinates (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j y)‖)
    (fun y ↦ ‖fullCurlGradient u j y‖) hB hw hP
    (integrable_rootGapDerivative_sq gamma hg chi modes u j)
    (integrable_projectorCoordinateDerivative_sq gamma hg chi modes u hu j)
    (((LocalSquaredGapGradient.continuous_fullCurlGradient u j).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (fun i : ↑centers ↦ P i.1) tau M hM a b ha hb
  simpa only [twoPointBudget, B, P, w] using h

/-- The density-to-cost comparison holds for genuine iterated integrals,
with either measurable order of the two input displacements. -/
theorem integral_twoPointDerivativeDensity_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (j : Fin 3) (M : T6 → ℝ) (hM : Integrable M) (hMn : ∀ q, 0 ≤ M q)
    (a b : T6 → T3) (ha : Measurable a) (hb : Measurable b) :
    (∫ x : T3, ∫ q : T6, M q *
      twoPointDerivativeDensity gamma chi modes u centers tau j (x - a q) (x - b q)) ≤
      ∫ x : T3, ∫ q : T6, M q *
        twoPointBudget gamma chi modes u centers tau j (x - a q) (x - b q) := by
  have hd := integrable_twoPointDerivativeDensity gamma hg chi modes u
    (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) centers hc tau j M hM hMn a b ha hb
  have hB := integrable_twoPointBudget gamma hg chi modes u hu centers hc tau j M hM a b ha hb
  have h := integral_mono_ae hd hB (show ∀ᵐ p ∂((volume : Measure T6).prod (volume : Measure T3)),
      M p.1 * twoPointDerivativeDensity gamma chi modes u centers tau j (p.2 - a p.1) (p.2 - b p.1) ≤
      M p.1 * twoPointBudget gamma chi modes u centers tau j (p.2 - a p.1) (p.2 - b p.1) from by
    filter_upwards [ae_translated_twoPointDerivativeDensity_le gamma hg chi modes u hu centers hc tau j a b ha]
      with p hp
    exact mul_le_mul_of_nonneg_left hp (hMn p.1))
  rw [integral_prod_symm _ hd, integral_prod_symm _ hB] at h
  exact h

open GaussianRootWeakPressureAction (rootInput)
open PressureKernelAction (kernelAction)
open PressureCoherentChannelPeriodization (periodicKernel)
open LocalGaussianPressurePartition (localDirection)
open PressureCoherentDivergenceChannel (Factor)
open PancakeBilinearPeriodization (firstTorusDisplacement secondTorusDisplacement)

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup

/-- Spatial energy of the actual localized channel outputs, with the squared
unit-torus derivative and input-frequency normalization retained. -/
def normalizedChannelEnergy (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (N : ℝ) (hN : 0 < N) (t : ℝ) (c : Factor) : ℝ :=
  (2 * Real.pi * N) ^ 2 * ∫ x : T3, ∑ i : ↑centers,
    ‖kernelAction (periodicKernel N hN t (localDirection chi modes u i.1) c)
      (rootInput gamma hg chi modes u hu centers hc tau i)
      (rootInput gamma hg chi modes u hu centers hc tau i) x‖ ^ 2

theorem normalizedChannelEnergy_nonneg (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (N : ℝ) (hN : 0 < N) (t : ℝ) (c : Factor) :
    0 ≤ normalizedChannelEnergy gamma hg chi modes u hu centers hc tau N hN t c :=
  mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))

theorem first_channel_sum_energy_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (N : ℝ) (hN : 0 < N) (t : ℝ) (j : Fin 3)
    (M : T6 → ℝ) (hM : Integrable M) (hMn : ∀ q, 0 ≤ M q)
    (hdom : ∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 →
      ‖periodicKernel N hN t e .undifferentiated q‖ ≤ M q) :
    let hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
    normalizedChannelEnergy gamma hg chi modes u hu2 centers hc tau N hN t (.first j) ≤
      (∫ q : T6, M q) * ∫ x : T3, ∫ q : T6, M q *
        twoPointBudget gamma chi modes u centers tau j
          (x - firstTorusDisplacement q) (x - secondTorusDisplacement q) := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  exact (GaussianRootWeakChannelBudget.first_channel_sum_energy_le gamma hg chi modes u hu2 centers hc tau
    N hN t j M hM hMn hdom).trans (mul_le_mul_of_nonneg_left
      (integral_twoPointDerivativeDensity_le gamma hg chi modes u hu centers hc tau j M hM hMn
        firstTorusDisplacement secondTorusDisplacement (by fun_prop) (by fun_prop))
      (integral_nonneg hMn))

theorem second_channel_sum_energy_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (N : ℝ) (hN : 0 < N) (t : ℝ) (j : Fin 3)
    (M : T6 → ℝ) (hM : Integrable M) (hMn : ∀ q, 0 ≤ M q)
    (hdom : ∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 →
      ‖periodicKernel N hN t e .undifferentiated q‖ ≤ M q) :
    let hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
    normalizedChannelEnergy gamma hg chi modes u hu2 centers hc tau N hN t (.second j) ≤
      (∫ q : T6, M q) * ∫ x : T3, ∫ q : T6, M q *
        twoPointBudget gamma chi modes u centers tau j
          (x - secondTorusDisplacement q) (x - firstTorusDisplacement q) := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  exact (GaussianRootWeakChannelBudget.second_channel_sum_energy_le gamma hg chi modes u hu2 centers hc tau
    N hN t j M hM hMn hdom).trans (mul_le_mul_of_nonneg_left
      (integral_twoPointDerivativeDensity_le gamma hg chi modes u hu centers hc tau j M hM hMn
        secondTorusDisplacement firstTorusDisplacement (by fun_prop) (by fun_prop))
      (integral_nonneg hMn))

/-- A constructed common envelope carries both integrated channel costs and
the relative second moment. All constants are uniform in input scale and
low-output parameter; the actual-data costs remain explicit. -/
theorem exists_uniform_channel_sum_envelope (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) :
    let hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M : (N : ℝ) → 0 < N → ℝ → T6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N, ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
        (∀ q, 0 ≤ M N hN t q) ∧ Measurable (M N hN t) ∧ Integrable (M N hN t) ∧
        Integrable (fun q ↦ ‖FrequencyPairPeriodization.relativeTorusDisplacement q‖ ^ 2 * M N hN t q) ∧
        (∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 → ∀ c : Factor,
          ‖periodicKernel N hN t e c q‖ ≤ M N hN t q) ∧
        (∫ q : T6, M N hN t q) ≤ PressureLowOutputCutoff.ratio t * C ∧
        (∫ q : T6, ‖FrequencyPairPeriodization.relativeTorusDisplacement q‖ ^ 2 * M N hN t q) ≤
          PressureLowOutputCutoff.ratio t * C * min ((1 / 2 : ℝ) ^ 2) (N⁻¹ ^ 2) ∧
        ∀ j : Fin 3,
          Integrable (fun p : T6 × T3 ↦ M N hN t p.1 *
            twoPointBudget gamma chi modes u centers tau j
              (p.2 - firstTorusDisplacement p.1) (p.2 - secondTorusDisplacement p.1))
            ((volume : Measure T6).prod (volume : Measure T3)) ∧
          Integrable (fun p : T6 × T3 ↦ M N hN t p.1 *
            twoPointBudget gamma chi modes u centers tau j
              (p.2 - secondTorusDisplacement p.1) (p.2 - firstTorusDisplacement p.1))
            ((volume : Measure T6).prod (volume : Measure T3)) ∧
          normalizedChannelEnergy gamma hg chi modes u hu2 centers hc tau N hN t (.first j) ≤
            PressureLowOutputCutoff.ratio t * C * ∫ x : T3, ∫ q : T6, M N hN t q *
              twoPointBudget gamma chi modes u centers tau j
                (x - firstTorusDisplacement q) (x - secondTorusDisplacement q) ∧
          normalizedChannelEnergy gamma hg chi modes u hu2 centers hc tau N hN t (.second j) ≤
            PressureLowOutputCutoff.ratio t * C * ∫ x : T3, ∫ q : T6, M N hN t q *
              twoPointBudget gamma chi modes u centers tau j
                (x - secondTorusDisplacement q) (x - firstTorusDisplacement q) := by
  obtain ⟨C, hC, M, hb⟩ := PressureCoherentRelativeMoment.exists_uniform_periodic_envelope 2
  refine ⟨C, hC, M, fun N hN t ht ↦ ?_⟩
  obtain ⟨hn, hm, hi, hmoment, hk, hmass, hrel⟩ := hb N hN t ht
  have hd : ∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 →
      ‖periodicKernel N hN t e .undifferentiated q‖ ≤ M N hN t q :=
    hk.mono (fun _ h e he ↦ h e he .undifferentiated)
  refine ⟨hn, hm, hi, hmoment, hk, hmass, hrel, fun j ↦ ?_⟩
  have hnB (a b : T6 → T3) : 0 ≤ ∫ x : T3, ∫ q : T6, M N hN t q *
      twoPointBudget gamma chi modes u centers tau j (x - a q) (x - b q) :=
    integral_nonneg (fun x ↦ integral_nonneg (fun q ↦ mul_nonneg (hn q)
      (twoPointBudget_nonneg gamma chi modes u centers hc tau j _ _)))
  refine ⟨integrable_twoPointBudget gamma hg chi modes u hu centers hc tau j (M N hN t) hi
      firstTorusDisplacement secondTorusDisplacement (by fun_prop) (by fun_prop),
    integrable_twoPointBudget gamma hg chi modes u hu centers hc tau j (M N hN t) hi
      secondTorusDisplacement firstTorusDisplacement (by fun_prop) (by fun_prop), ?_, ?_⟩
  · exact (first_channel_sum_energy_le gamma hg chi modes u hu centers hc tau N hN t j
      (M N hN t) hi hn hd).trans
      (mul_le_mul_of_nonneg_right hmass (hnB firstTorusDisplacement secondTorusDisplacement))
  · exact (second_channel_sum_energy_le gamma hg chi modes u hu centers hc tau N hN t j
      (M N hN t) hi hn hd).trans
      (mul_le_mul_of_nonneg_right hmass (hnB secondTorusDisplacement firstTorusDisplacement))

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointIntegral
