import Mettapedia.Analysis.RootPartitionTwoPointEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootWeakChannelBudget

/-!
# Two-point cost of the actual localized weak derivatives

The partner root weight is evaluated at an arbitrary second point on one
full-measure set of derivative points. Gaussian overlap replaces the patch
sum by a two-point projector moment. The gap-factor derivative, projector
derivative, vorticity powers, and temperature remain explicit costs.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointDerivative

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierTranslationCurve
open LocalLowDiffusionBudget LocalSquaredGapPressure LocalSpatialVorticityJets
open PancakeHigherDerivativeMoments GaussianRootVorticity GaussianRootDifference GaussianRootWeakDivergence
open GaussianRootWeakChannelBudget
open Mettapedia.Analysis.EuclideanOperatorCoordinates Mettapedia.Analysis.RootPartitionEnergy
open Mettapedia.Analysis.GaussianPartitionEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "X3" => Fin 3 → ℝ
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def twoPointBudget (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (j : Fin 3) (y z : T3) : ℝ :=
  let b := fun x : T3 ↦ rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) x)
  let M := fun x : T3 ↦ coordinates (localProjector gamma chi modes u x)
  2 * b z ^ 2 * ‖fullVorticity u z‖ ^ 3 * ‖fullVorticity u y‖ ^ 3 *
    (2 * deriv (fun h ↦ b (y + coordinateShift j h)) 0 ^ 2 +
      b y ^ 2 / tau ^ 2 * ‖coordinates (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j y)‖ ^ 2 *
        twoPointDistanceMoment (fun i : ↑centers ↦ M i.1) tau (M y) (M z)) +
    8 * b z ^ 2 * b y ^ 2 * ‖fullVorticity u z‖ ^ 3 * ‖fullVorticity u y‖ * ‖fullCurlGradient u j y‖ ^ 2

theorem ae_twoPointDerivativeDensity_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (j : Fin 3) :
    ∀ᵐ y : T3, ∀ z : T3,
      twoPointDerivativeDensity gamma chi modes u centers tau j y z ≤
        twoPointBudget gamma chi modes u centers tau j y z := by
  letI : Nonempty ↑centers := ⟨⟨hc.choose, hc.choose_spec⟩⟩
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hS := PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u)
  have hlS : LocallyLipschitz
      (fun r : X3 ↦ spatialStrain modes (filteredVelocity chi u) (torusPoint r)) :=
    fun r ↦ (LocalSpatialBottomProjector.contDiff_spatialStrain (n := 1) chi modes u).locallyLipschitz r
  have hb := PancakePeriodicWeakDerivative.ae_coordinate_differentiable
    (fun x ↦ rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) x)) j
    ((locallyLipschitz_rootGapFactor gamma hg).continuous.comp hS)
    ((locallyLipschitz_rootGapFactor gamma hg).comp hlS)
  have hM := LocalSquaredGapGradient.ae_coordinate_differentiable gamma hg chi modes u hu2 j
  have hd (i : ↑centers) := ae_hasDerivAt_coordinateDerivative gamma hg chi modes u hu2 centers hc tau i j
  filter_upwards [hb, hM, ae_all_iff.mpr hd] with y hby hMy hdy
  intro z
  have hcoord := (coordinates (ι := Fin 3)).hasFDerivAt.comp_hasDerivAt 0 hMy.hasDerivAt
  have hw := hasDerivAt_fullVorticity_shift u hu j y 0
  have h := sum_twoPoint_rootVorticity_deriv_sq_le
    (fun i : ↑centers ↦ coordinates (localProjector gamma chi modes u i.1)) tau
    hby.hasDerivAt hcoord hw (rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) z))
    (coordinates (localProjector gamma chi modes u z)) (fullVorticity u z)
  have heq (i : ↑centers) := (hdy i).deriv
  simp only [rootVorticity_eq_factor, gaussianFactor] at heq
  simpa only [twoPointDerivativeDensity, twoPointBudget, rootPatch_eq_factor, rootVorticity_eq_factor,
    rootFieldFactor, rootAmplitude, gaussianFactor, Function.comp_def,
    PancakeHaarTransportRate.coordinateShift_zero, add_zero,
    LocalSquaredGapGradient.coordinateDerivative, heq] using h

def localizedTwoPointBudget (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (j : Fin 3) (k : ↑centers) (y z : T3) : ℝ :=
  let b := fun x : T3 ↦ rootGapFactor gamma (spatialStrain modes (filteredVelocity chi u) x)
  let M := fun x : T3 ↦ coordinates (localProjector gamma chi modes u x)
  2 * b z ^ 2 * ‖fullVorticity u z‖ ^ 3 * ‖fullVorticity u y‖ ^ 3 *
    (2 * deriv (fun h ↦ b (y + coordinateShift j h)) 0 ^ 2 +
      b y ^ 2 / tau ^ 2 * ‖coordinates (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j y)‖ ^ 2 *
        (2 * ‖M y - M k.1‖ ^ 2 + ‖M z - M k.1‖ ^ 2 + 3 * tau * Real.log (Fintype.card ↑centers))) +
    8 * b z ^ 2 * b y ^ 2 * ‖fullVorticity u z‖ ^ 3 * ‖fullVorticity u y‖ * ‖fullCurlGradient u j y‖ ^ 2

theorem twoPointBudget_le_localized (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (ht : 0 < tau)
    (j : Fin 3) (k : ↑centers) (y z : T3) :
    twoPointBudget gamma chi modes u centers tau j y z ≤
      localizedTwoPointBudget gamma chi modes u centers tau j k y z := by
  letI : Nonempty ↑centers := ⟨k⟩
  dsimp only [twoPointBudget, localizedTwoPointBudget]
  gcongr
  exact twoPointDistanceMoment_le _ tau ht _ _ k

theorem ae_twoPointDerivativeDensity_le_localized (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (ht : 0 < tau) (j : Fin 3) :
    ∀ᵐ y : T3, ∀ z : T3, ∀ k : ↑centers,
      twoPointDerivativeDensity gamma chi modes u centers tau j y z ≤
        localizedTwoPointBudget gamma chi modes u centers tau j k y z := by
  filter_upwards [ae_twoPointDerivativeDensity_le gamma hg chi modes u hu centers hc tau j] with y hy
  intro z k
  exact (hy z).trans (twoPointBudget_le_localized gamma chi modes u centers tau ht j k y z)

/-- The common null set survives the actual displacement of the derivative
point. This is the product-measure inequality needed before integration. -/
theorem ae_translated_twoPointDerivativeDensity_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (j : Fin 3) (a b : T6 → T3) (ha : Measurable a) :
    ∀ᵐ p ∂((volume : Measure T6).prod (volume : Measure T3)),
      twoPointDerivativeDensity gamma chi modes u centers tau j (p.2 - a p.1) (p.2 - b p.1) ≤
        twoPointBudget gamma chi modes u centers tau j (p.2 - a p.1) (p.2 - b p.1) := by
  have h := ae_twoPointDerivativeDensity_le gamma hg chi modes u hu centers hc tau j
  have hp : ∀ᵐ p ∂((volume : Measure T6).prod (volume : Measure T3)), ∀ z : T3,
      twoPointDerivativeDensity gamma chi modes u centers tau j p.2 z ≤
        twoPointBudget gamma chi modes u centers tau j p.2 z :=
    (MeasureTheory.Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure T6)) (ν := (volume : Measure T3))).tendsto_ae.eventually h
  have hs := (Mettapedia.Analysis.BilinearTranslatedKernel.measurePreserving_skew_sub
    (μ := (volume : Measure T6)) (ν := (volume : Measure T3)) a ha).quasiMeasurePreserving.tendsto_ae.eventually hp
  filter_upwards [hs] with p hpp
  exact hpp (p.2 - b p.1)

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootTwoPointDerivative
