import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootVorticity

/-!
# Actual root patches with fourth-power coverage and regular weighted fields

The old adaptive cover is reused. Multiplying its squared amplitudes by an
additional squared gap gate gives the exact weight required after localizing
both pressure inputs. The original collision term is enlarged explicitly.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootPartition

open scoped BigOperators
open MeasureTheory
open Mettapedia.Analysis.GaussianPartitionEnergy Mettapedia.Analysis.EuclideanOperatorCoordinates
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeSpectralFiniteDifference
open PancakeSpectralProjectorRegularity.SymmetricStrain
open LocalLowDiffusionBudget LocalSquaredGapPressure LocalGaussianPressurePartition
open GaussianRootVorticity SpectralGapTiltWeight SpectralTiltFreezing AdaptiveGaussianLinePartition
open PancakeHigherDerivativeMoments PancakeFourierTranslationCurve

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem rootPatch_fourth_eq (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (i : ↑centers) (x : T3) :
    rootPatch gamma chi modes u centers tau i x ^ 4 =
      gapCutoff gamma (topGap (spatialStrain modes (filteredVelocity chi u) x)) ^ 2 *
        patch gamma chi modes u centers tau i x ^ 2 := by
  rw [show rootPatch gamma chi modes u centers tau i x ^ 4 =
    (rootPatch gamma chi modes u centers tau i x ^ 2) ^ 2 by ring,
    rootPatch_sq_eq_gated_patch gamma hg chi modes u centers hc tau, mul_pow]

theorem sum_rootPatch_fourth (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (x : T3) :
    (∑ i : ↑centers, rootPatch gamma chi modes u centers tau i x ^ 4) =
      QuarticGapTiltWeight.weight gamma (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x) := by
  letI : Nonempty ↑centers := ⟨⟨hc.choose, hc.choose_spec⟩⟩
  simp only [rootPatch_fourth_eq gamma hg chi modes u centers hc tau,
    patch_eq_amplitude_mul_gaussianFactor gamma hg, mul_pow, ← Finset.mul_sum,
    gaussianFactor, sum_gaussianAmplitude_sq, mul_one, QuarticGapTiltWeight.weight,
    SquaredGapTiltWeight.weight, localAmplitude]

theorem continuous_rootPatch (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) : Continuous (rootPatch gamma chi modes u centers tau i) := by
  letI : Nonempty ↑centers := ⟨⟨hc.choose, hc.choose_spec⟩⟩
  have hS := PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u)
  have hM := (coordinates (ι := Fin 3)).continuous.comp (continuous_localProjector gamma hg chi modes u hu)
  have htheta := (continuous_gaussianAmplitude
    (fun j : ↑centers ↦ coordinates (localProjector gamma chi modes u j.1)) tau i).comp hM
  exact (((locallyLipschitz_rootGapFactor gamma hg).continuous.comp hS).mul
    (continuous_fullVorticity u hu).norm.sqrt).mul htheta.sqrt

theorem continuous_rootVorticity (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) : Continuous (rootVorticity gamma chi modes u centers tau i) :=
  (continuous_rootPatch gamma hg chi modes u hu centers hc tau i).smul (continuous_fullVorticity u hu)

theorem ae_differentiable_rootVorticity_lift (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) :
    ∀ᵐ r : X3, DifferentiableAt ℝ
      (fun s : X3 ↦ rootVorticity gamma chi modes u centers tau i (torusPoint s)) r :=
  (locallyLipschitz_rootVorticity gamma hg chi modes u hu centers hc tau i).ae_differentiableAt volume

theorem exists_local_root_partition (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (rho : ℝ) (hrho : 0 < rho) :
    ∃ centers : Finset T3, centers.Nonempty ∧
      let tau := temperature centers.card rho
      let c := rootPatch gamma chi modes u centers tau
      0 < tau ∧ (∀ i, Continuous (c i)) ∧
      (∀ x, (∑ i, c i x ^ 4) = QuarticGapTiltWeight.weight gamma
        (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x)) ∧
      (∀ x, (∑ i, c i x ^ 4 *
        lineDistanceSq (localDirection chi modes u x) (localDirection chi modes u i.1)) ≤ rho ^ 2) ∧
      (∀ i, LocallyLipschitz (fun r : X3 ↦ c i (torusPoint r) • fullVorticity u (torusPoint r))) := by
  obtain ⟨centers, hc, ht, _, _, hline, _, _⟩ := exists_local_gaussian_partition gamma hg chi modes u hu rho hrho
  refine ⟨centers, hc, ht, ?_, ?_, ?_, ?_⟩
  · exact fun i ↦ continuous_rootPatch gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc _ i
  · exact fun x ↦ sum_rootPatch_fourth gamma hg chi modes u centers hc _ x
  · intro x
    simp only [rootPatch_fourth_eq gamma hg chi modes u centers hc,
      mul_assoc, ← Finset.mul_sum]
    have h0 := gapCutoff_nonneg gamma (topGap (spatialStrain modes (filteredVelocity chi u) x))
    have h1 := gapCutoff_le_one gamma (topGap (spatialStrain modes (filteredVelocity chi u) x))
    have h := mul_le_mul_of_nonneg_left (hline x)
      (sq_nonneg (gapCutoff gamma (topGap (spatialStrain modes (filteredVelocity chi u) x))))
    exact h.trans ((mul_le_mul_of_nonneg_right (by nlinarith :
      gapCutoff gamma (topGap (spatialStrain modes (filteredVelocity chi u) x)) ^ 2 ≤ 1)
      (sq_nonneg rho)).trans_eq (one_mul _))
  · exact fun i ↦ locallyLipschitz_rootVorticity gamma hg chi modes u hu centers hc _ i

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootPartition
