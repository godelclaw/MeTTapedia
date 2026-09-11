import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootPartition

/-!
# Actual root-weighted vorticity derivatives without inverse vorticity

The scalar factor here contains the gap ramp and normalized Gaussian, not
the square root of the vorticity magnitude. That radial factor is kept with
the vorticity. Its derivative budget vanishes rather than diverges at zero.
No scale-uniform bound on the remaining scalar-factor derivatives is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootDifferentiation

open scoped BigOperators
open MeasureTheory Mettapedia.Analysis.RadialSquareRoot Mettapedia.Analysis.GaussianPartitionEnergy
open Mettapedia.Analysis.EuclideanOperatorCoordinates
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierTranslationCurve
open LocalLowDiffusionBudget LocalSquaredGapPressure LocalGaussianPressurePartition
open GaussianRootVorticity GaussianRootPartition LocalSpatialVorticityJets PancakeHigherDerivativeMoments
open PancakeSpectralProjectorRegularity.SymmetricStrain SpectralGapTiltWeight SpectralDiffusionWeightLimit
open LocalJointSourceTilt LocalAlignmentForcing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuous_rootFieldFactor (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) : Continuous (rootFieldFactor gamma chi modes u centers tau i) := by
  letI : Nonempty ↑centers := ⟨⟨hc.choose, hc.choose_spec⟩⟩
  have hS := PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u)
  have hM := (coordinates (ι := Fin 3)).continuous.comp (continuous_localProjector gamma hg chi modes u hu)
  have htheta := (continuous_gaussianAmplitude
    (fun j : ↑centers ↦ coordinates (localProjector gamma chi modes u j.1)) tau i).comp hM
  exact ((locallyLipschitz_rootGapFactor gamma hg).continuous.comp hS).mul htheta.sqrt

theorem ae_coordinate_rootVorticity_derivative_budget (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) (j : Fin 3) :
    ∀ᵐ x : T3,
      DifferentiableAt ℝ (fun h ↦ rootVorticity gamma chi modes u centers tau i (x + coordinateShift j h)) 0 ∧
      ‖deriv (fun h ↦ rootVorticity gamma chi modes u centers tau i (x + coordinateShift j h)) 0‖ ^ 2 ≤
        2 * deriv (fun h ↦ rootFieldFactor gamma chi modes u centers tau i (x + coordinateShift j h)) 0 ^ 2 *
          ‖fullVorticity u x‖ ^ 3 +
        8 * rootFieldFactor gamma chi modes u centers tau i x ^ 2 * ‖fullVorticity u x‖ *
          ‖fullCurlGradient u j x‖ ^ 2 := by
  have ha := PancakePeriodicWeakDerivative.ae_coordinate_differentiable
    (rootFieldFactor gamma chi modes u centers tau i) j
    (continuous_rootFieldFactor gamma hg chi modes u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu) centers hc tau i)
    (locallyLipschitz_rootFieldFactor gamma hg chi modes u (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) centers hc tau i)
  filter_upwards [ha] with x hx
  have hw := hasDerivAt_fullVorticity_shift u hu j x 0
  have heq : (fun h ↦ rootVorticity gamma chi modes u centers tau i (x + coordinateShift j h)) =
      (fun h ↦ rootFieldFactor gamma chi modes u centers tau i (x + coordinateShift j h) •
        radialSqrt (fullVorticity u (x + coordinateShift j h))) := by
    funext h
    exact rootVorticity_eq_factor gamma chi modes u centers tau i _
  rw [heq]
  constructor
  · exact hx.smul ((differentiable_radialSqrt _).comp 0 hw.differentiableAt)
  · simpa only [PancakeHaarTransportRate.coordinateShift_zero, add_zero] using
      norm_deriv_smul_radialSqrt_sq_le hx.hasDerivAt hw

theorem sourceExcess_le_quartic_jointTilt_add_collision (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    LocalTiltSource.sourceExcess chi modes outputs u x ≤
      gapCutoff gamma (topGap S) ^ 4 *
        (max (2 * ‖nonviscousRemainder chi modes outputs u x‖ - topGap S ^ 2 / 8) 0 * limitingWeight S (fullVorticity u x)) +
      8 * QuarticGapTiltWeight.weight gamma S (fullVorticity u x) * ‖jointTilt chi modes outputs u x‖ ^ 2 +
      QuarticGapTiltWeight.collisionCost gamma S (nonviscousRemainder chi modes outputs u x) (fullVorticity u x) := by
  simpa only [LocalTiltSource.sourceExcess, SpectralTiltExcess.tiltNorm_eq, jointTilt] using
    QuarticGapTiltWeight.excess_le_weighted_tilt_add_collision gamma hg
      (spatialStrain modes (filteredVelocity chi u) x)
      (nonviscousRemainder chi modes outputs u x) (fullVorticity u x)

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootDifferentiation
