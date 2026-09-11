import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootPartition
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureTraceSymbol
import Mettapedia.Analysis.SquaredWeightLocalization
import Mettapedia.Analysis.ScaledPartitionDerivative

/-!
# Localization through the squared Gaussian root patches

The nonnegative roots permit a sum-of-squares bound by differences of
their squares. These squares equal the original Gaussian patches times
the common gap gate and are locally Lipschitz. Their actual derivative
energy retains the gate derivative and the previous patch-gradient cost.
No patch-count factor, inverse vorticity, or scalar-root derivative enters.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootLocalization

open MeasureTheory
open Mettapedia.Analysis.SquaredWeightLocalization Mettapedia.Analysis.ScaledPartitionDerivative
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator FourierPressureTraceSymbol
open PancakeFourierTranslationCurve PancakeHigherDerivativeMoments PancakeFilteredStrainDynamics
open PancakeFourierMaterialPaths PancakeSpectralFiniteDifference
open PancakeSpectralProjectorRegularity.SymmetricStrain
open LocalLowDiffusionBudget LocalGaussianPressurePartition GaussianRootVorticity GaussianRootPartition
open SpectralGapTiltWeight LocalSquaredGapPressure

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem rootPatch_nonneg (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x : T3) :
    0 ≤ rootPatch gamma chi modes u centers tau i x := by
  have h := gapCutoff_nonneg gamma (topGap (spatialStrain modes (filteredVelocity chi u) x))
  unfold rootPatch rootGapFactor
  positivity

theorem locallyLipschitz_rootPatch_sq (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) :
    LocallyLipschitz (fun r : X3 ↦ rootPatch gamma chi modes u centers tau i (torusPoint r) ^ 2) := by
  simp_rw [rootPatch_sq_eq_gated_patch gamma hg chi modes u centers hc tau]
  have hS : LocallyLipschitz (fun r : X3 ↦ spatialStrain modes (filteredVelocity chi u) (torusPoint r)) :=
    fun r ↦ (LocalSpatialBottomProjector.contDiff_spatialStrain (n := 1) chi modes u).locallyLipschitz r
  exact (((locallyLipschitz_gapCutoff gamma hg).comp locallyLipschitz_topGap).comp hS).mul_algebra
    (locallyLipschitz_patch gamma hg chi modes u hu centers hc tau i)

theorem ae_coordinate_differentiable_rootPatch_sq (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) (j : Fin 3) :
    ∀ᵐ x : T3, DifferentiableAt ℝ
      (fun h ↦ rootPatch gamma chi modes u centers tau i (x + coordinateShift j h) ^ 2) 0 :=
  PancakePeriodicWeakDerivative.ae_coordinate_differentiable _ j
    ((continuous_rootPatch gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau i).pow 2)
    (locallyLipschitz_rootPatch_sq gamma hg chi modes u hu centers hc tau i)

def squaredPatchDifference (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (x y : T3) : ℝ :=
  ∑ i : ↑centers, (rootPatch gamma chi modes u centers tau i x ^ 2 -
    rootPatch gamma chi modes u centers tau i y ^ 2) ^ 2

theorem sum_norm_rootLocalization_integrand_sq_le
    (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (x y z : T3)
    (B : ↑centers → Op) (L : ℝ) (hB : ∀ i, ‖B i‖ ≤ L) :
    let c := rootPatch gamma chi modes u centers tau
    let w := fun x ↦ complexifyVector (fullVorticity u x)
    (∑ i : ↑centers, ‖((c i x : ℂ) * (c i x : ℂ)) • B i (w y) (w z) -
      B i ((c i y : ℂ) • w y) ((c i z : ℂ) • w z)‖ ^ 2) ≤
      L ^ 2 * ‖fullVorticity u y‖ ^ 2 * ‖fullVorticity u z‖ ^ 2 *
        (squaredPatchDifference gamma chi modes u centers tau x y +
          squaredPatchDifference gamma chi modes u centers tau x z) := by
  simpa only [norm_complexifyVector, squaredPatchDifference] using
    sum_norm_localization_sq_le Finset.univ B
      (fun i ↦ rootPatch gamma chi modes u centers tau i x)
      (fun i ↦ rootPatch gamma chi modes u centers tau i y)
      (fun i ↦ rootPatch gamma chi modes u centers tau i z)
      (fun i _ ↦ mul_nonneg (rootPatch_nonneg gamma chi modes u centers tau i y)
        (rootPatch_nonneg gamma chi modes u centers tau i z))
      (complexifyVector (fullVorticity u y)) (complexifyVector (fullVorticity u z)) L (fun i _ ↦ hB i)

theorem ae_coordinate_rootPatch_sq_derivative_bound (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (j : Fin 3) :
    let g := fun x ↦ gapCutoff gamma (topGap (spatialStrain modes (filteredVelocity chi u) x))
    ∀ᵐ x : T3,
      (∑ i : ↑centers, deriv (fun h ↦
        rootPatch gamma chi modes u centers tau i (x + coordinateShift j h) ^ 2) 0 ^ 2) ≤
      2 * deriv (fun h ↦ g (x + coordinateShift j h)) 0 ^ 2 *
        (∑ i : ↑centers, patch gamma chi modes u centers tau i x ^ 2) +
      2 * g x ^ 2 * ∑ i : ↑centers,
        deriv (fun h ↦ patch gamma chi modes u centers tau i (x + coordinateShift j h)) 0 ^ 2 := by
  dsimp only
  have hS := PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u)
  have hSl : LocallyLipschitz
      (fun r : X3 ↦ spatialStrain modes (filteredVelocity chi u) (torusPoint r)) :=
    fun r ↦ (LocalSpatialBottomProjector.contDiff_spatialStrain (n := 1) chi modes u).locallyLipschitz r
  have hgate := (locallyLipschitz_gapCutoff gamma hg).comp locallyLipschitz_topGap
  have hgd := PancakePeriodicWeakDerivative.ae_coordinate_differentiable
    (fun x ↦ gapCutoff gamma (topGap (spatialStrain modes (filteredVelocity chi u) x))) j
    (hgate.continuous.comp hS) (hgate.comp hSl)
  have hpd (i : ↑centers) := ae_coordinate_differentiable_patch gamma hg chi modes u hu centers hc tau i j
  filter_upwards [hgd, ae_all_iff.mpr hpd] with x hx hp
  simp_rw [rootPatch_sq_eq_gated_patch gamma hg chi modes u centers hc tau]
  simpa only [PancakeHaarTransportRate.coordinateShift_zero, add_zero] using
    sum_deriv_mul_sq_le Finset.univ hx.hasDerivAt (fun i _ ↦ (hp i).hasDerivAt)

end Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootLocalization
