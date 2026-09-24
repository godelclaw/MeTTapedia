import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.BoundedGaussianLinePartition
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalGapGateGradient

/-!
# Uniform geometry multipliers for the actual Gaussian root gradients

The cover-size bound depends on vorticity size, gap threshold, and line
tolerance, but not on the frequency cutoff or the oscillation of the strain.
The squared-root patch energy is controlled by actual vorticity and filtered
strain gradients. These derivative costs are retained, not assumed bounded
in time. The final existence theorem constructs its adaptive patch family.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.UniformGaussianGradientBudget

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeFilteredStrainDynamics PancakeFourierStrainGradient
open PancakeFourierMaterialPaths
open PancakeFourierTranslationCurve PancakeHaarTransportRate LocalSpatialVorticityJets
open LocalLowDiffusionBudget LocalSquaredGapPressure LocalGaussianPressurePartition
open AdaptiveGaussianLinePartition BoundedGaussianLinePartition SpectralTiltFreezing
open GaussianSquaredRootTranslation LocalGapGateGradient SpectralGapTiltWeight

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def partitionMultiplier (M : ℕ) (gamma W rho : ℝ) : ℝ :=
  3 * (1 + (W / gamma) ^ 2 * rho ^ 2 / (2 * temperature M rho ^ 2))

theorem partitionMultiplier_nonneg (M : ℕ) (gamma W rho : ℝ) :
    0 ≤ partitionMultiplier M gamma W rho := by unfold partitionMultiplier; positivity

def gradientDensity (gamma W A : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  (4 * A / gamma ^ 2) * (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) +
    ((72 + 1600 * A) * W ^ 2 / gamma ^ 4) *
      (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2)

theorem continuous_gradientDensity (gamma W A : ℝ) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) : Continuous (gradientDensity gamma W A chi modes u) := by
  have hw := LocalSquaredGapGradient.continuous_fullCurlGradient u
  have hS := LocalStrainGradientDensity.continuous_strainGradient chi modes u
  unfold gradientDensity
  fun_prop

theorem localAmplitude_le (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (W : ℝ)
    (hW : ∀ x : T3, ‖fullVorticity u x‖ ≤ W) (x : T3) :
    localAmplitude gamma chi modes u x ≤ W / gamma := by
  unfold localAmplitude SquaredGapTiltWeight.amplitude
  calc
    _ ≤ ‖fullVorticity u x‖ / max _ gamma :=
      div_le_div_of_nonneg_right
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (gapCutoff_le_one gamma _) (norm_nonneg _))
        (hg.le.trans (le_max_right _ _))
    _ ≤ ‖fullVorticity u x‖ / gamma :=
      div_le_div_of_nonneg_left (norm_nonneg _) hg (le_max_right _ _)
    _ ≤ _ := div_le_div_of_nonneg_right (hW x) hg.le

theorem ae_rootGradient_le_of_patch_bound (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (W A : ℝ) (hA : 0 ≤ A)
    (hW : ∀ x : T3, ‖fullVorticity u x‖ ≤ W)
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ)
    (hmass : ∀ x, (∑ i : ↑centers, patch gamma chi modes u centers tau i x ^ 2) =
      localWeight gamma chi modes u x)
    (hpatch : ∀ᵐ x : T3, patchGradientSquare gamma chi modes u centers tau x ≤
      A * LocalSquaredGapGradient.gradientSquare gamma chi modes u x) :
    ∀ᵐ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x ≤
      gradientDensity gamma W A chi modes u x := by
  have hroot := ae_squaredRootGradientSquare_le gamma hg chi modes u
    (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) centers hc tau
  filter_upwards [hroot, hpatch] with x hx hp
  have hweight : localWeight gamma chi modes u x ≤ (W / gamma) ^ 2 :=
    pow_le_pow_left₀ (SquaredGapTiltWeight.amplitude_nonneg gamma hg _ _)
      (localAmplitude_le gamma hg chi modes u W hW x) 2
  have hWsq := pow_le_pow_left₀ (norm_nonneg _) (hW x) 2
  have hS : 0 ≤ ∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hg0 := gapCutoff_nonneg gamma (PancakeSpectralProjectorRegularity.SymmetricStrain.topGap
    (spatialStrain modes (filteredVelocity chi u) x))
  have hg1 := gapCutoff_le_one gamma (PancakeSpectralProjectorRegularity.SymmetricStrain.topGap
    (spatialStrain modes (filteredVelocity chi u) x))
  have hgate : gate gamma chi modes u x ^ 2 ≤ 1 := by dsimp [gate]; nlinarith
  have hp0 : 0 ≤ patchGradientSquare gamma chi modes u centers tau x :=
    Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  have hD := LocalSquaredGapGradient.gradientSquare_le gamma hg chi modes u hu x
  have hD' : LocalSquaredGapGradient.gradientSquare gamma chi modes u x ≤
      (2 / gamma ^ 2) * (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) +
        (800 * W ^ 2 / gamma ^ 4) *
          (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2) := by
    apply hD.trans
    gcongr
  change squaredRootGradientSquare gamma chi modes u centers tau x ≤
    2 * PeriodicFourierGradientEnergy.gradientSquare (gate gamma chi modes u) x *
      (∑ i : ↑centers, patch gamma chi modes u centers tau i x ^ 2) +
      2 * gate gamma chi modes u x ^ 2 * patchGradientSquare gamma chi modes u centers tau x at hx
  rw [hmass] at hx
  calc
    _ ≤ _ := hx
    _ ≤ 2 * ((36 / gamma ^ 2) * ∑ j : Fin 3,
          ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2) * (W / gamma) ^ 2 +
        2 * (A * ((2 / gamma ^ 2) * (∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) +
          (800 * W ^ 2 / gamma ^ 4) *
            (∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2))) := by
      apply add_le_add
      · apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (gradientSquare_gate_le gamma hg chi modes u x) (by norm_num)
        · exact hweight
        · exact sq_nonneg _
        · positivity
      · calc
          _ ≤ 2 * patchGradientSquare gamma chi modes u centers tau x := by nlinarith
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (hp.trans (mul_le_mul_of_nonneg_left hD' hA)) (by norm_num)
    _ = _ := by unfold gradientDensity; ring

/-- The common geometry constants are chosen before the filter, mode set,
and velocity. The actual derivative density is constructed afterwards. -/
theorem exists_uniform_root_gradient_budget (gamma : ℝ) (hg : 0 < gamma)
    (W rho : ℝ) (hrho : 0 < rho) :
    ∃ M : ℕ, 0 < M ∧ ∀ chi : Wavevector → ℂ, ∀ modes : Finset Wavevector,
      ∀ u : FourierVelocity, Summable (fourierMoment 3 u) →
      (∀ x : T3, ‖fullVorticity u x‖ ≤ W) →
      ∃ centers : Finset T3, centers.Nonempty ∧ centers.card ≤ M ∧
        let tau := temperature centers.card rho
        let A := partitionMultiplier M gamma W rho
        0 < temperature M rho ∧ temperature M rho ≤ tau ∧
        (∀ x, (∑ i : ↑centers, patch gamma chi modes u centers tau i x ^ 2) =
          localWeight gamma chi modes u x) ∧
        (∀ x, (∑ i : ↑centers, patch gamma chi modes u centers tau i x ^ 2 *
          lineDistanceSq (localDirection chi modes u x) (localDirection chi modes u i.1)) ≤ rho ^ 2) ∧
        Integrable (squaredRootGradientSquare gamma chi modes u centers tau) ∧
        (∀ᵐ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x ≤
          gradientDensity gamma W A chi modes u x) ∧
        (∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x) ≤
          ∫ x : T3, gradientDensity gamma W A chi modes u x := by
  obtain ⟨M, hM, h⟩ := exists_bounded_gaussian_line_partition (X := T3) (W / gamma) rho hrho
  refine ⟨M, hM, ?_⟩
  intro chi modes u hu hW
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hcont := continuous_localProjector gamma hg chi modes u hu1
  change Continuous (fun x ↦ localProjector gamma chi modes u x) at hcont
  simp_rw [localProjector_eq gamma hg] at hcont
  obtain ⟨centers, hc, hcard, hT, hTle, _, hmass, hline, hpath⟩ :=
    h (localAmplitude gamma chi modes u) (fun _ ↦ SquaredGapTiltWeight.amplitude_nonneg gamma hg _ _)
      (localAmplitude_le gamma hg chi modes u W hW) (localDirection chi modes u)
      (fun _ ↦ PancakeSpectralFiniteDifference.topVector_norm _) hcont
  let tau := temperature centers.card rho
  let A := partitionMultiplier M gamma W rho
  have hmass' (x : T3) : (∑ i : ↑centers, patch gamma chi modes u centers tau i x ^ 2) =
      localWeight gamma chi modes u x := by
    simpa only [patch_eq_lineAmplitude gamma hg, localWeight, SquaredGapTiltWeight.weight, localAmplitude] using hmass x
  have hline' (x : T3) : (∑ i : ↑centers, patch gamma chi modes u centers tau i x ^ 2 *
      lineDistanceSq (localDirection chi modes u x) (localDirection chi modes u i.1)) ≤ rho ^ 2 := by
    simpa only [patch_eq_lineAmplitude gamma hg] using hline x
  have hp : ∀ᵐ x : T3, patchGradientSquare gamma chi modes u centers tau x ≤
      A * LocalSquaredGapGradient.gradientSquare gamma chi modes u x := by
    have hd (j : Fin 3) := LocalSquaredGapGradient.ae_coordinate_differentiable gamma hg chi modes u hu2 j
    filter_upwards [ae_all_iff.mpr hd] with x hx
    unfold patchGradientSquare LocalSquaredGapGradient.gradientSquare
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hderiv : HasDerivAt (fun h : ℝ ↦ localProjector gamma chi modes u (x + coordinateShift j h))
        (LocalSquaredGapGradient.coordinateDerivative gamma chi modes u j x) 0 := (hx j).hasDerivAt
    simp_rw [localProjector_eq gamma hg] at hderiv
    have hb := hpath (fun h ↦ x + coordinateShift j h) 0 _ hderiv
    simpa only [patch_eq_lineAmplitude gamma hg, coordinateShift_zero, add_zero,
      A, partitionMultiplier, LocalSquaredGapGradient.coordinateDerivative] using hb
  have hbound := ae_rootGradient_le_of_patch_bound gamma hg chi modes u hu W A
    (partitionMultiplier_nonneg M gamma W rho) hW centers hc tau hmass' hp
  have hi := integrable_squaredRootGradientSquare gamma hg chi modes u hu2 centers hc tau
  have hdi : Integrable (gradientDensity gamma W A chi modes u) :=
    (continuous_gradientDensity gamma W A chi modes u).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  exact ⟨centers, hc, hcard, hT, hTle, hmass', hline', hi, hbound, integral_mono_ae hi hdi hbound⟩

end Mettapedia.FluidDynamics.NavierStokes.UniformGaussianGradientBudget
