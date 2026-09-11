import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.AdaptiveGaussianLinePartition
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSquaredGapGradient
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicWeakDerivative
import Mettapedia.Analysis.GaussianPartitionRegularity

/-!
# Quantitative patches of the actual squared-gap projector

The patches are constructed from the filtered strain and full vorticity.
The same finite family has exact squared coverage, a weighted line error
bound, and almost-everywhere spatial derivative control. No positive
spectral gap is assumed. The logarithmic cover-size and inverse-threshold
costs are retained; this is not a uniform dynamical estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalGaussianPressurePartition

open scoped BigOperators
open MeasureTheory
open Mettapedia.Analysis.EuclideanOperatorCoordinates Mettapedia.Analysis.GaussianPartitionEnergy
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeSpectralFiniteDifference
open PancakeFourierTranslationCurve PancakeHigherDerivativeMoments PancakeHaarTransportRate
open LocalLowDiffusionBudget LocalSquaredGapPressure SpectralTiltFreezing
open GaussianWeightedLinePartition AdaptiveGaussianLinePartition

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def localAmplitude (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  SquaredGapTiltWeight.amplitude gamma (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x)

def localDirection (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 := topVector (spatialStrain modes (filteredVelocity chi u) x)

def patch (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x : T3) : ℝ :=
  normScaledAmplitude (fun j : ↑centers ↦ coordinates (localProjector gamma chi modes u j.1)) tau
    (coordinates (localProjector gamma chi modes u x)) i

def patchGradientSquare (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (x : T3) : ℝ :=
  ∑ j : Fin 3, ∑ i : ↑centers,
    deriv (fun h : ℝ ↦ patch gamma chi modes u centers tau i (x + coordinateShift j h)) 0 ^ 2

theorem localProjector_eq (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    localProjector gamma chi modes u x = localAmplitude gamma chi modes u x •
      InnerProductSpace.rankOne ℝ (localDirection chi modes u x) (localDirection chi modes u x) := by
  rw [localProjector, SquaredGapTiltWeight.weightedProjector_eq gamma hg,
    SquaredGapTiltWeight.sqrt_weight gamma hg]
  rfl

theorem patch_eq_lineAmplitude (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x : T3) :
    patch gamma chi modes u centers tau i x =
      lineAmplitude (fun j : ↑centers ↦ localAmplitude gamma chi modes u j.1)
        (fun j : ↑centers ↦ localDirection chi modes u j.1) tau
        (localAmplitude gamma chi modes u x) (localDirection chi modes u x) i := by
  simp only [patch, localProjector_eq gamma hg, lineAmplitude, coordinateProjector]

theorem continuous_patch (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) : Continuous (patch gamma chi modes u centers tau i) := by
  letI : Nonempty ↑centers := ⟨⟨hc.choose, hc.choose_spec⟩⟩
  exact (continuous_normScaledAmplitude _ tau i).comp
    ((coordinates (ι := Fin 3)).continuous.comp (continuous_localProjector gamma hg chi modes u hu))

theorem locallyLipschitz_patch (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) :
    LocallyLipschitz (fun r : X3 ↦ patch gamma chi modes u centers tau i (torusPoint r)) := by
  letI : Nonempty ↑centers := ⟨⟨hc.choose, hc.choose_spec⟩⟩
  exact (locallyLipschitz_normScaledAmplitude _ tau i).comp
    ((coordinates (ι := Fin 3)).lipschitz.locallyLipschitz.comp
      (locallyLipschitz_localProjector gamma hg chi modes u hu))

/-- Genuine differentiability, separately from the total-derivative bound. -/
theorem ae_coordinate_differentiable_patch (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) (j : Fin 3) :
    ∀ᵐ x : T3, DifferentiableAt ℝ
      (fun h : ℝ ↦ patch gamma chi modes u centers tau i (x + coordinateShift j h)) 0 := by
  exact PancakePeriodicWeakDerivative.ae_coordinate_differentiable _ j
    (continuous_patch gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau i)
    (locallyLipschitz_patch gamma hg chi modes u hu centers hc tau i)

theorem stronglyMeasurable_patchGradientSquare (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) : StronglyMeasurable (patchGradientSquare gamma chi modes u centers tau) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro j _
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  apply StronglyMeasurable.pow
  have hjoint : Continuous (fun z : T3 × ℝ ↦ patch gamma chi modes u centers tau i
      (z.1 + coordinateShift j z.2)) :=
    (continuous_patch gamma hg chi modes u hu centers hc tau i).comp
      (continuous_fst.add ((continuous_coordinateShift j).comp continuous_snd))
  exact Continuous.stronglyMeasurable_deriv_const
    (f := fun x h ↦ patch gamma chi modes u centers tau i (x + coordinateShift j h)) hjoint 0

theorem exists_local_gaussian_partition (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (rho : ℝ) (hrho : 0 < rho) :
    ∃ centers : Finset T3, centers.Nonempty ∧
      let tau := temperature centers.card rho
      let p := patch gamma chi modes u centers tau
      0 < tau ∧ (∀ i, Continuous (p i)) ∧
      (∀ x, (∑ i, p i x ^ 2) = localWeight gamma chi modes u x) ∧
      (∀ x, (∑ i, p i x ^ 2 *
        lineDistanceSq (localDirection chi modes u x) (localDirection chi modes u i.1)) ≤ rho ^ 2) ∧
      (∀ i j, ∀ᵐ x : T3, DifferentiableAt ℝ (fun h : ℝ ↦ p i (x + coordinateShift j h)) 0) ∧
      (∀ᵐ x : T3, patchGradientSquare gamma chi modes u centers tau x ≤
        3 * (1 + localWeight gamma chi modes u x * rho ^ 2 / (2 * tau ^ 2)) *
          LocalSquaredGapGradient.gradientSquare gamma chi modes u x) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu
  have hM := continuous_localProjector gamma hg chi modes u hu1
  change Continuous (fun x ↦ localProjector gamma chi modes u x) at hM
  simp_rw [localProjector_eq gamma hg] at hM
  obtain ⟨centers, hc, ht, _, hmass, hline, hpath⟩ :=
    exists_gaussian_line_partition (localAmplitude gamma chi modes u)
      (fun _ ↦ SquaredGapTiltWeight.amplitude_nonneg gamma hg _ _)
      (localDirection chi modes u) (fun _ ↦ topVector_norm _) hM rho hrho
  let tau := temperature centers.card rho
  refine ⟨centers, hc, ht, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i ↦ continuous_patch gamma hg chi modes u hu1 centers hc tau i
  · intro x
    simpa only [patch_eq_lineAmplitude gamma hg, localWeight, SquaredGapTiltWeight.weight, localAmplitude] using hmass x
  · intro x
    simpa only [patch_eq_lineAmplitude gamma hg] using hline x
  · exact fun i j ↦ ae_coordinate_differentiable_patch gamma hg chi modes u hu centers hc tau i j
  · have hd (j : Fin 3) := LocalSquaredGapGradient.ae_coordinate_differentiable gamma hg chi modes u hu j
    filter_upwards [ae_all_iff.mpr hd] with x hx
    unfold patchGradientSquare LocalSquaredGapGradient.gradientSquare
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hderiv : HasDerivAt
        (fun h : ℝ ↦ localProjector gamma chi modes u (x + coordinateShift j h))
        (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j x) 0 := (hx j).hasDerivAt
    simp_rw [localProjector_eq gamma hg] at hderiv
    have h := hpath (fun h ↦ x + coordinateShift j h) 0
      (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j x) hderiv
    simpa only [patch_eq_lineAmplitude gamma hg, coordinateShift_zero, add_zero, localWeight, SquaredGapTiltWeight.weight,
      localAmplitude] using h

end Mettapedia.FluidDynamics.NavierStokes.LocalGaussianPressurePartition
