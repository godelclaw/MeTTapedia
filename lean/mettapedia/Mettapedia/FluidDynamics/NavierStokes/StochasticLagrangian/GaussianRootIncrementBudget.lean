import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SquaredGapProjectorIncrement
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootTwoPointIntegral

/-!
# Actual field increments in the integrated Gaussian channel cost

A cover of the weighted projector image replaces the two-point Gaussian
moment by an explicit localization error and actual vorticity/strain
increments. Both input orders retain their full derivative-weighted cost.
The resulting integrals are genuine; no uniform-in-time bound is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootIncrementBudget

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierTranslationCurve
open LocalLowDiffusionBudget LocalSquaredGapPressure LocalSpatialVorticityJets
open PancakeHigherDerivativeMoments GaussianRootVorticity GaussianRootTwoPointDerivative
open GaussianRootTwoPointIntegral
open Mettapedia.Analysis.EuclideanOperatorCoordinates Mettapedia.Analysis.GaussianPartitionEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def incrementMoment (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau epsilon : ℝ) (y z : T3) : ℝ :=
  4 * epsilon ^ 2 + 12 * (‖fullVorticity u y - fullVorticity u z‖ / gamma) ^ 2 +
    4800 * (‖fullVorticity u z‖ *
      ‖(spatialStrain modes (filteredVelocity chi u) y).1 -
        (spatialStrain modes (filteredVelocity chi u) z).1‖ / gamma ^ 2) ^ 2 +
    3 * tau * Real.log (centers.card : ℝ)

theorem twoPointDistanceMoment_le_incrementMoment (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) (ht : 0 < tau) (epsilon : ℝ)
    (hcover : ∀ y : T3, ∃ k ∈ centers,
      ‖coordinates (localProjector gamma chi modes u y) -
        coordinates (localProjector gamma chi modes u k)‖ ≤ epsilon) (y z : T3) :
    twoPointDistanceMoment (fun i : ↑centers ↦ coordinates (localProjector gamma chi modes u i.1)) tau
      (coordinates (localProjector gamma chi modes u y)) (coordinates (localProjector gamma chi modes u z)) ≤
      incrementMoment gamma chi modes u centers tau epsilon y z := by
  obtain ⟨k, hk, hclose⟩ := hcover y
  letI : Nonempty ↑centers := ⟨⟨k, hk⟩⟩
  have h := twoPointDistanceMoment_le_separation
    (fun i : ↑centers ↦ coordinates (localProjector gamma chi modes u i.1)) tau ht
    (coordinates (localProjector gamma chi modes u y)) (coordinates (localProjector gamma chi modes u z)) ⟨k, hk⟩
  have hs := pow_le_pow_left₀ (norm_nonneg _) hclose 2
  have hp := SquaredGapTiltWeight.norm_coordinates_weightedProjector_sub_sq_le gamma hg
    (spatialStrain modes (filteredVelocity chi u) y) (spatialStrain modes (filteredVelocity chi u) z)
    (fullVorticity u y) (fullVorticity u z)
  change ‖coordinates (localProjector gamma chi modes u y) -
    coordinates (localProjector gamma chi modes u z)‖ ^ 2 ≤ _ at hp
  simp only [Fintype.card_coe] at h
  dsimp only [incrementMoment]
  linarith only [h, hs, hp]

theorem continuous_incrementMoment (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (centers : Finset T3) (tau epsilon : ℝ) :
    Continuous (fun p : T3 × T3 ↦ incrementMoment gamma chi modes u centers tau epsilon p.1 p.2) := by
  have hw := continuous_fullVorticity u hu
  have hS : Continuous (fun x : T3 ↦ (spatialStrain modes (filteredVelocity chi u) x).1) :=
    continuous_subtype_val.comp (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
  unfold incrementMoment
  exact ((continuous_const.add
    (((((hw.comp continuous_fst).sub (hw.comp continuous_snd)).norm.div_const gamma).pow 2).const_mul 12)).add
      (((((hw.comp continuous_snd).norm.mul
        ((hS.comp continuous_fst).sub (hS.comp continuous_snd)).norm).div_const (gamma ^ 2)).pow 2).const_mul 4800)).add
    continuous_const

def incrementBudget (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau epsilon : ℝ) (j : Fin 3) (y z : T3) : ℝ :=
  let b := fun x : T3 ↦ rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) x)
  2 * b z ^ 2 * ‖fullVorticity u z‖ ^ 3 * ‖fullVorticity u y‖ ^ 3 *
    (2 * deriv (fun h ↦ b (y + coordinateShift j h)) 0 ^ 2 +
      b y ^ 2 / tau ^ 2 * ‖coordinates (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j y)‖ ^ 2 *
        incrementMoment gamma chi modes u centers tau epsilon y z) +
    8 * b z ^ 2 * b y ^ 2 * ‖fullVorticity u z‖ ^ 3 * ‖fullVorticity u y‖ * ‖fullCurlGradient u j y‖ ^ 2

theorem twoPointBudget_le_incrementBudget (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) (ht : 0 < tau) (epsilon : ℝ)
    (hcover : ∀ y : T3, ∃ k ∈ centers,
      ‖coordinates (localProjector gamma chi modes u y) -
        coordinates (localProjector gamma chi modes u k)‖ ≤ epsilon) (j : Fin 3) (y z : T3) :
    twoPointBudget gamma chi modes u centers tau j y z ≤
      incrementBudget gamma chi modes u centers tau epsilon j y z := by
  dsimp only [twoPointBudget, incrementBudget]
  gcongr
  exact twoPointDistanceMoment_le_incrementMoment gamma hg chi modes u centers tau ht epsilon hcover y z

theorem integrable_incrementBudget (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (tau epsilon : ℝ) (j : Fin 3)
    (M : T6 → ℝ) (hM : Integrable M) (a b : T6 → T3) (ha : Measurable a) (hb : Measurable b) :
    Integrable (fun p : T6 × T3 ↦ M p.1 *
      incrementBudget gamma chi modes u centers tau epsilon j (p.2 - a p.1) (p.2 - b p.1))
      ((volume : Measure T6).prod (volume : Measure T3)) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  let B := fun x : T3 ↦ rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) x)
  have hB : Continuous B := (locallyLipschitz_rootGapFactor gamma hg).continuous.comp
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
  exact Mettapedia.Analysis.RootPartitionEnergy.integrable_twoPointDerivativeCost_of_continuous
    B (fun x ↦ ‖fullVorticity u x‖) (fun y ↦ deriv (fun h ↦ B (y + coordinateShift j h)) 0)
    (fun y ↦ ‖coordinates (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j y)‖)
    (fun y ↦ ‖fullCurlGradient u j y‖) hB (continuous_fullVorticity u hu1).norm
    (integrable_rootGapDerivative_sq gamma hg chi modes u j)
    (integrable_projectorCoordinateDerivative_sq gamma hg chi modes u hu j)
    (((LocalSquaredGapGradient.continuous_fullCurlGradient u j).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ⟨_, continuous_incrementMoment gamma chi modes u hu1 centers tau epsilon⟩ tau M hM a b ha hb

theorem integral_twoPointBudget_le_incrementBudget (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (ht : 0 < tau) (epsilon : ℝ)
    (hcover : ∀ y : T3, ∃ k ∈ centers,
      ‖coordinates (localProjector gamma chi modes u y) -
        coordinates (localProjector gamma chi modes u k)‖ ≤ epsilon)
    (j : Fin 3) (M : T6 → ℝ) (hM : Integrable M) (hMn : ∀ q, 0 ≤ M q)
    (a b : T6 → T3) (ha : Measurable a) (hb : Measurable b) :
    (∫ x : T3, ∫ q : T6, M q * twoPointBudget gamma chi modes u centers tau j (x - a q) (x - b q)) ≤
      ∫ x : T3, ∫ q : T6, M q * incrementBudget gamma chi modes u centers tau epsilon j (x - a q) (x - b q) := by
  have h0 := integrable_twoPointBudget gamma hg chi modes u hu centers hc tau j M hM a b ha hb
  have h1 := integrable_incrementBudget gamma hg chi modes u hu centers tau epsilon j M hM a b ha hb
  have h := integral_mono h0 h1 (fun p ↦ mul_le_mul_of_nonneg_left
    (twoPointBudget_le_incrementBudget gamma hg chi modes u centers tau ht epsilon hcover j _ _) (hMn p.1))
  rw [integral_prod_symm _ h0, integral_prod_symm _ h1] at h
  exact h

open PressureCoherentChannelPeriodization (periodicKernel)
open PancakeBilinearPeriodization (firstTorusDisplacement secondTorusDisplacement)

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- Both actual input-coordinate channel energies are paid by the increment
cost, with the second channel retaining the reversed endpoint order. -/
theorem channel_sum_energy_le_incrementBudget (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (ht : 0 < tau) (epsilon : ℝ)
    (hcover : ∀ y : T3, ∃ k ∈ centers,
      ‖coordinates (localProjector gamma chi modes u y) -
        coordinates (localProjector gamma chi modes u k)‖ ≤ epsilon)
    (N : ℝ) (hN : 0 < N) (t : ℝ) (j : Fin 3)
    (M : T6 → ℝ) (hM : Integrable M) (hMn : ∀ q, 0 ≤ M q)
    (hdom : ∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 →
      ‖periodicKernel N hN t e .undifferentiated q‖ ≤ M q) :
    let hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
    normalizedChannelEnergy gamma hg chi modes u hu2 centers hc tau N hN t (.first j) ≤
      (∫ q : T6, M q) * ∫ x : T3, ∫ q : T6, M q *
        incrementBudget gamma chi modes u centers tau epsilon j
          (x - firstTorusDisplacement q) (x - secondTorusDisplacement q) ∧
    normalizedChannelEnergy gamma hg chi modes u hu2 centers hc tau N hN t (.second j) ≤
      (∫ q : T6, M q) * ∫ x : T3, ∫ q : T6, M q *
        incrementBudget gamma chi modes u centers tau epsilon j
          (x - secondTorusDisplacement q) (x - firstTorusDisplacement q) := by
  constructor
  · exact (first_channel_sum_energy_le gamma hg chi modes u hu centers hc tau N hN t j M hM hMn hdom).trans
      (mul_le_mul_of_nonneg_left (integral_twoPointBudget_le_incrementBudget gamma hg chi modes u hu centers hc
        tau ht epsilon hcover j M hM hMn firstTorusDisplacement secondTorusDisplacement (by fun_prop) (by fun_prop))
        (integral_nonneg hMn))
  · exact (second_channel_sum_energy_le gamma hg chi modes u hu centers hc tau N hN t j M hM hMn hdom).trans
      (mul_le_mul_of_nonneg_left (integral_twoPointBudget_le_incrementBudget gamma hg chi modes u hu centers hc
        tau ht epsilon hcover j M hM hMn secondTorusDisplacement firstTorusDisplacement (by fun_prop) (by fun_prop))
        (integral_nonneg hMn))

/-- Centers are selected from the actual field, not an assumed spatial grid.
Their number is not asserted to be uniformly bounded as the field evolves. -/
theorem exists_projector_increment_cover (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ centers : Finset T3, centers.Nonempty ∧
      (∀ y : T3, ∃ k ∈ centers,
        ‖coordinates (localProjector gamma chi modes u y) -
          coordinates (localProjector gamma chi modes u k)‖ ≤ epsilon) ∧
      ∀ tau : ℝ, 0 < tau → ∀ j y z,
        twoPointBudget gamma chi modes u centers tau j y z ≤
          incrementBudget gamma chi modes u centers tau epsilon j y z := by
  obtain ⟨centers, hcover⟩ := PancakeAdaptiveStrainCover.exists_finite_adaptive_freezing_cover
    (fun y : T3 ↦ coordinates (localProjector gamma chi modes u y))
    ((coordinates (ι := Fin 3)).continuous.comp (continuous_localProjector gamma hg chi modes u hu)) he
  have hc : centers.Nonempty := by
    obtain ⟨k, hk, _⟩ := hcover 0
    exact ⟨k, hk⟩
  have hclose : ∀ y : T3, ∃ k ∈ centers,
      ‖coordinates (localProjector gamma chi modes u y) -
        coordinates (localProjector gamma chi modes u k)‖ ≤ epsilon := by
    intro y
    obtain ⟨k, hk, h⟩ := hcover y
    exact ⟨k, hk, h.le⟩
  exact ⟨centers, hc, hclose, fun tau ht j y z ↦
    twoPointBudget_le_incrementBudget gamma hg chi modes u centers tau ht epsilon hclose j y z⟩

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootIncrementBudget
