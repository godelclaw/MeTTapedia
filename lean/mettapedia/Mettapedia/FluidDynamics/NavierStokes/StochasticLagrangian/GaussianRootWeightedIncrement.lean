import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootIncrementBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicWeightedIncrement

/-!
# Weighted vorticity increments in Gaussian channel costs

The bare vorticity increment is paid by sixth-power-weighted palinstrophy,
with the actual kernel envelope retaining its relative second-moment gain.
The derivative of the weighted projector remains a separate two-endpoint
coefficient. No estimate on its time evolution or on palinstrophy is assumed
to have been proved by the spatial translation argument.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeightedIncrement

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierTranslationCurve
open PancakeHaarTransportRate LocalLowDiffusionBudget LocalSquaredGapPressure LocalSpatialVorticityJets
open PancakeHigherDerivativeMoments GaussianRootVorticity GaussianRootTwoPointIntegral
open PeriodicWeightedIncrement PeriodicVectorWeakDerivative
open Mettapedia.Analysis.EuclideanOperatorCoordinates Mettapedia.Analysis.RadialPower
open FrequencyPairPeriodization PressureLowOutputCutoff
open PancakeBilinearPeriodization (firstTorusDisplacement secondTorusDisplacement)
open PressureCoherentChannelPeriodization (periodicKernel)
open PressureCoherentDivergenceChannel (Factor)

local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def weightedPalinstrophyDensity (u : FourierVelocity) (x : T3) : ℝ :=
  ‖fullVorticity u x‖ ^ 6 * ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2

theorem coordinateRate_fullVorticity (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) (x : T3) : coordinateRate (fullVorticity u) j x = fullCurlGradient u j x := by
  ext i
  have h := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_fullVorticity_shift u hu j x 0)
  simpa only [coordinateRate_apply, shiftRate, Function.comp_def, PiLp.proj_apply,
    coordinateShift_zero, add_zero] using h.deriv

theorem weightedGradientDensity_fullVorticity (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (x : T3) :
    weightedGradientDensity (fullVorticity u) x = weightedPalinstrophyDensity u x := by
  simp only [weightedGradientDensity, gradientDensity, weightedPalinstrophyDensity,
    coordinateRate_fullVorticity u hu]

/-- One actual envelope works for every admissible snapshot, every direction,
and every channel. The weighted palinstrophy on the right is not bounded in time. -/
theorem exists_uniform_vorticity_increment_envelope :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M : (N : ℝ) → 0 < N → ℝ → T6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N, ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
        (∀ q, 0 ≤ M N hN t q) ∧ Measurable (M N hN t) ∧ Integrable (M N hN t) ∧
        (∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 → ∀ c : Factor,
          ‖periodicKernel N hN t e c q‖ ≤ M N hN t q) ∧
        (∫ q : T6, M N hN t q) ≤ ratio t * C ∧
        ∀ u : FourierVelocity, Summable (fourierMoment 3 u) →
          (∫ x : T3, ∫ q : T6, M N hN t q * incrementDensity (fullVorticity u)
            (x - firstTorusDisplacement q) (x - secondTorusDisplacement q)) ≤
          48 * (ratio t * C * min ((1 / 2 : ℝ) ^ 2) (N⁻¹ ^ 2)) *
            ∫ x : T3, weightedPalinstrophyDensity u x := by
  obtain ⟨C, hC, M, hM⟩ := PressureCoherentRelativeMoment.exists_uniform_periodic_envelope 2
  refine ⟨C, hC, M, fun N hN t ht ↦ ?_⟩
  obtain ⟨hn, hm, hi, hmoment, hdom, hmass, hbound⟩ := hM N hN t ht
  refine ⟨hn, hm, hi, hdom, hmass, fun u hu ↦ ?_⟩
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have h := integral_envelope_incrementDensity_le (fullVorticity u) (continuous_fullVorticity u hu1)
    (LocalAlignmentTransport.locallyLipschitz_fullVorticity u hu2)
    (M N hN t) hi hn firstTorusDisplacement secondTorusDisplacement
    (by fun_prop) (by fun_prop) hmoment
  simp only [weightedGradientDensity_fullVorticity u hu] at h
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (by norm_num))
    (integral_nonneg (fun x ↦ by unfold weightedPalinstrophyDensity; positivity)))

/-- The complete coefficient of the vorticity increment in `incrementBudget`.
It depends on both endpoints, not just the differentiated endpoint. -/
def incrementCoefficient (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (tau : ℝ) (j : Fin 3) (y z : T3) : ℝ :=
  24 * rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) z) ^ 2 *
    rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) y) ^ 2 / tau ^ 2 *
    ‖coordinates (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j y)‖ ^ 2 / gamma ^ 2

def vorticityIncrementCost (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (tau : ℝ) (j : Fin 3) (y z : T3) : ℝ :=
  2 * rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) z) ^ 2 *
    ‖fullVorticity u z‖ ^ 3 * ‖fullVorticity u y‖ ^ 3 *
    (rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) y) ^ 2 / tau ^ 2 *
      ‖coordinates (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j y)‖ ^ 2 *
      (12 * (‖fullVorticity u y - fullVorticity u z‖ / gamma) ^ 2))

theorem vorticityIncrementCost_eq (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (tau : ℝ) (j : Fin 3) (y z : T3) :
    vorticityIncrementCost gamma chi modes u tau j y z =
      incrementCoefficient gamma chi modes u tau j y z * incrementDensity (fullVorticity u) y z := by
  simp only [vorticityIncrementCost, incrementCoefficient, incrementDensity, div_pow]
  ring

/-- All other terms of the existing channel cost, including the strain
increment and both local derivatives. None is absorbed by the radial lemma. -/
def remainderBudget (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau epsilon : ℝ) (j : Fin 3) (y z : T3) : ℝ :=
  let b := fun x : T3 ↦ rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) x)
  let H := 4 * epsilon ^ 2 +
    4800 * (‖fullVorticity u z‖ *
      ‖(spatialStrain modes (filteredVelocity chi u) y).1 -
        (spatialStrain modes (filteredVelocity chi u) z).1‖ / gamma ^ 2) ^ 2 +
    3 * tau * Real.log (centers.card : ℝ)
  2 * b z ^ 2 * ‖fullVorticity u z‖ ^ 3 * ‖fullVorticity u y‖ ^ 3 *
    (2 * deriv (fun h ↦ b (y + coordinateShift j h)) 0 ^ 2 +
      b y ^ 2 / tau ^ 2 * ‖coordinates (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j y)‖ ^ 2 * H) +
    8 * b z ^ 2 * b y ^ 2 * ‖fullVorticity u z‖ ^ 3 * ‖fullVorticity u y‖ * ‖fullCurlGradient u j y‖ ^ 2

theorem incrementBudget_eq_remainder_add_cost (gamma : ℝ) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (centers : Finset T3) (tau epsilon : ℝ)
    (j : Fin 3) (y z : T3) :
    GaussianRootIncrementBudget.incrementBudget gamma chi modes u centers tau epsilon j y z =
      remainderBudget gamma chi modes u centers tau epsilon j y z +
        vorticityIncrementCost gamma chi modes u tau j y z := by
  dsimp only [GaussianRootIncrementBudget.incrementBudget, GaussianRootIncrementBudget.incrementMoment,
    remainderBudget, vorticityIncrementCost]
  ring

theorem vorticityIncrementCost_le_radial_increment (gamma : ℝ) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (tau : ℝ) (j : Fin 3) (y z : T3) :
    vorticityIncrementCost gamma chi modes u tau j y z ≤
      incrementCoefficient gamma chi modes u tau j y z *
        ‖radialPower 3 (fullVorticity u y) - radialPower 3 (fullVorticity u z)‖ ^ 2 := by
  rw [vorticityIncrementCost_eq]
  exact mul_le_mul_of_nonneg_left
    (product_weighted_norm_sub_sq_le 3 (fullVorticity u y) (fullVorticity u z))
    (by unfold incrementCoefficient; positivity)

theorem integrable_coefficient_mul_continuous (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (tau : ℝ) (j : Fin 3) (H : C(T3 × T3, ℝ))
    (M : T6 → ℝ) (hM : Integrable M) (a b : T6 → T3) (ha : Measurable a) (hb : Measurable b) :
    Integrable (fun p : T6 × T3 ↦ M p.1 *
      (incrementCoefficient gamma chi modes u tau j (p.2 - a p.1) (p.2 - b p.1) *
        H (p.2 - a p.1, p.2 - b p.1)))
      ((volume : Measure T6).prod (volume : Measure T3)) := by
  let B := fun x : T3 ↦ rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) x)
  have hB : Continuous B := (locallyLipschitz_rootGapFactor gamma hg).continuous.comp
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
  let c : C(T3 × T3, ℝ) := ⟨fun p ↦ 24 * B p.2 ^ 2 * B p.1 ^ 2 / tau ^ 2 / gamma ^ 2 * H p,
    (((((hB.comp continuous_snd).pow 2).const_mul 24).mul
      ((hB.comp continuous_fst).pow 2)).div_const _ |>.div_const _).mul H.continuous⟩
  have h := Mettapedia.Analysis.BilinearTranslatedCoefficient.integrable_weighted_translate_mul_continuous
    M (fun y ↦ ‖coordinates (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j y)‖ ^ 2)
    hM (integrable_projectorCoordinateDerivative_sq gamma hg chi modes u hu j) a b ha hb c
  apply h.congr
  filter_upwards [] with p
  dsimp only [c, ContinuousMap.coe_mk, incrementCoefficient, B]
  ring

/-- A bounded-coefficient corollary explicitly exposes the remaining cost `A`.
This theorem does not construct a frequency- or time-uniform bound for `A`. -/
theorem integral_vorticityIncrementCost_le_of_coefficient_bound (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (tau : ℝ) (j : Fin 3) (A : ℝ) (hA : 0 ≤ A)
    (hcoeff : ∀ y z, incrementCoefficient gamma chi modes u tau j y z ≤ A)
    (M : T6 → ℝ) (hM : Integrable M) (hMn : ∀ q, 0 ≤ M q)
    (a b : T6 → T3) (ha : Measurable a) (hb : Measurable b)
    (hm : Integrable (fun q ↦ ‖a q - b q‖ ^ 2 * M q)) :
    (∫ x : T3, ∫ q : T6, M q * vorticityIncrementCost gamma chi modes u tau j (x - a q) (x - b q)) ≤
      A * (48 * (∫ q : T6, ‖a q - b q‖ ^ 2 * M q) * ∫ x : T3, weightedPalinstrophyDensity u x) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hf := continuous_fullVorticity u hu1
  let H : C(T3 × T3, ℝ) := ⟨_, continuous_incrementDensity (fullVorticity u) hf⟩
  have hi := integrable_coefficient_mul_continuous gamma hg chi modes u hu tau j H M hM a b ha hb
  have hj := (integrable_envelope_incrementDensity (fullVorticity u) hf M hM a b ha hb).const_mul A
  have h := integral_mono hi hj (fun p ↦ by
    dsimp only [H, ContinuousMap.coe_mk]
    calc
      _ ≤ M p.1 * (A * incrementDensity (fullVorticity u) (p.2 - a p.1) (p.2 - b p.1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hcoeff _ _)
          (by unfold incrementDensity; positivity)) (hMn p.1)
      _ = _ := by ring)
  rw [integral_prod_symm _ hi, integral_prod_symm _ hj] at h
  simp only [H, ContinuousMap.coe_mk, ← vorticityIncrementCost_eq, integral_const_mul] at h
  have hbnd := integral_envelope_incrementDensity_le (fullVorticity u) hf
    (LocalAlignmentTransport.locallyLipschitz_fullVorticity u hu2) M hM hMn a b ha hb hm
  simp only [weightedGradientDensity_fullVorticity u hu] at hbnd
  exact h.trans (mul_le_mul_of_nonneg_left hbnd hA)

theorem integral_incrementBudget_le_remainder_add_weightedPalinstrophy
    (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (centers : Finset T3) (tau epsilon : ℝ) (j : Fin 3) (A : ℝ) (hA : 0 ≤ A)
    (hcoeff : ∀ y z, incrementCoefficient gamma chi modes u tau j y z ≤ A)
    (M : T6 → ℝ) (hM : Integrable M) (hMn : ∀ q, 0 ≤ M q)
    (a b : T6 → T3) (ha : Measurable a) (hb : Measurable b)
    (hm : Integrable (fun q ↦ ‖a q - b q‖ ^ 2 * M q)) :
    (∫ x : T3, ∫ q : T6, M q *
      GaussianRootIncrementBudget.incrementBudget gamma chi modes u centers tau epsilon j (x - a q) (x - b q)) ≤
      (∫ x : T3, ∫ q : T6, M q * remainderBudget gamma chi modes u centers tau epsilon j (x - a q) (x - b q)) +
        A * (48 * (∫ q : T6, ‖a q - b q‖ ^ 2 * M q) * ∫ x : T3, weightedPalinstrophyDensity u x) := by
  have hf := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hc : Integrable (fun p : T6 × T3 ↦ M p.1 *
      vorticityIncrementCost gamma chi modes u tau j (p.2 - a p.1) (p.2 - b p.1))
      ((volume : Measure T6).prod (volume : Measure T3)) := by
    simpa only [vorticityIncrementCost_eq, ContinuousMap.coe_mk] using
      integrable_coefficient_mul_continuous gamma hg chi modes u hu tau j
        ⟨_, continuous_incrementDensity (fullVorticity u) hf⟩ M hM a b ha hb
  have hi := GaussianRootIncrementBudget.integrable_incrementBudget gamma hg chi modes u hu
    centers tau epsilon j M hM a b ha hb
  have he (p : T6 × T3) : M p.1 *
      GaussianRootIncrementBudget.incrementBudget gamma chi modes u centers tau epsilon j (p.2 - a p.1) (p.2 - b p.1) -
      M p.1 * vorticityIncrementCost gamma chi modes u tau j (p.2 - a p.1) (p.2 - b p.1) =
      M p.1 * remainderBudget gamma chi modes u centers tau epsilon j (p.2 - a p.1) (p.2 - b p.1) := by
    rw [incrementBudget_eq_remainder_add_cost]
    ring
  have hr := (hi.sub hc).congr (Filter.Eventually.of_forall he)
  have heq := integral_sub hi hc
  simp_rw [he] at heq
  rw [integral_prod_symm _ hr, integral_prod_symm _ hi, integral_prod_symm _ hc] at heq
  have h := integral_vorticityIncrementCost_le_of_coefficient_bound gamma hg chi modes u hu tau j
    A hA hcoeff M hM hMn a b ha hb hm
  linarith only [heq, h]

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeightedIncrement
