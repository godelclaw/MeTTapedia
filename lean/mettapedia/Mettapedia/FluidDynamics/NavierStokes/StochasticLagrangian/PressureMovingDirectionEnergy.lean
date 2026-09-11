import Mettapedia.Analysis.OddMapWeightedContinuity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootDirectionFreezing

/-!
# Continuous pressure energy for the actual moving spectral line

Only the weighted projector is required to be continuous. The signed top
eigenvector is neither assumed measurable nor differentiated. Oddness of
the full high-input action and its uniform direction estimate make the
weighted norm continuous, including on the zero-weight collision region.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureMovingDirectionEnergy

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFilteredStrainDynamics PancakeSpectralFiniteDifference LocalLowDiffusionBudget
open PancakeFourierMaterialPaths
open LocalSquaredGapPressure LocalGaussianPressurePartition PressureHighInputAction
open SpectralGapTiltWeight PancakeSpectralProjectorRegularity.SymmetricStrain
open PressureDirectionAction PressureDirectionParity

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "Field" => C(T3, C3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuous_localAmplitude (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : Continuous (localAmplitude gamma chi modes u) := by
  have h := (SquaredGapTiltWeight.continuous_weight gamma hg _ _
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
    (continuous_fullVorticity u hu)).sqrt
  change Continuous (fun x ↦ SquaredGapTiltWeight.amplitude gamma
    (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x))
  simpa only [SquaredGapTiltWeight.sqrt_weight gamma hg] using h

theorem continuous_weighted_norm (N : ℝ) (hN : 0 < N) (J : ℕ)
    (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (f g : Field) :
    Continuous (fun x ↦ localAmplitude gamma chi modes u x *
      ‖tailOperator N hN J (localDirection chi modes u x) f g x‖) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_field_bound
  apply Mettapedia.Analysis.OddMapWeightedContinuity.continuous_weighted_norm
    (fun e x ↦ tailOperator N hN J e f g x)
    (fun x e ↦ by simp only [tailOperator_neg]; rfl)
    ((C * (1 / 4 : ℝ) ^ J) * ‖f‖ * ‖g‖) (by positivity)
    (fun x e r he hr ↦ (hb N hN J e r he hr f g x).trans_eq (by ring))
    (fun e _ ↦ (tailOperator N hN J e f g).continuous)
    (localAmplitude gamma chi modes u) (continuous_localAmplitude gamma hg chi modes u hu)
    (localDirection chi modes u) (fun _ ↦ topVector_norm _)
    (localProjector gamma chi modes u) (continuous_localProjector gamma hg chi modes u hu)
  intro x y
  have h := WeightedLineFreezing.sq_mul_lineDistanceSq_le
    (localDirection chi modes u x) (localDirection chi modes u y)
    (topVector_norm _) (topVector_norm _)
    (localAmplitude gamma chi modes u x) (localAmplitude gamma chi modes u y)
  simpa only [SpectralTiltFreezing.lineDistanceSq, ← localProjector_eq gamma hg] using h

def energy (N : ℝ) (hN : 0 < N) (J : ℕ) (gamma : ℝ) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (f g : Field) (x : T3) : ℝ :=
  QuarticGapTiltWeight.weight gamma (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x) *
    ‖tailOperator N hN J (localDirection chi modes u x) f g x‖ ^ 2

theorem energy_nonneg (N : ℝ) (hN : 0 < N) (J : ℕ) (gamma : ℝ) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (f g : Field) (x : T3) :
    0 ≤ energy N hN J gamma chi modes u f g x :=
  mul_nonneg (QuarticGapTiltWeight.weight_nonneg _ _ _) (sq_nonneg _)

theorem energy_eq_zero_of_vorticity_eq_zero (N : ℝ) (hN : 0 < N) (J : ℕ)
    (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (f g : Field) (x : T3) (hw : fullVorticity u x = 0) :
    energy N hN J gamma chi modes u f g x = 0 := by
  simp [energy, QuarticGapTiltWeight.weight, SquaredGapTiltWeight.weight,
    SquaredGapTiltWeight.amplitude, hw]

theorem energy_eq_zero_of_topGap_le (N : ℝ) (hN : 0 < N) (J : ℕ)
    (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (f g : Field) (x : T3)
    (hgap : topGap (spatialStrain modes (filteredVelocity chi u) x) ≤ gamma) :
    energy N hN J gamma chi modes u f g x = 0 := by
  simp [energy, QuarticGapTiltWeight.weight, gapCutoff_eq_zero gamma _ hg hgap]

theorem continuous_energy (N : ℝ) (hN : 0 < N) (J : ℕ)
    (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (f g : Field) :
    Continuous (energy N hN J gamma chi modes u f g) := by
  have hgap := StrainEigenvalueContinuity.continuous_topGap.comp
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
  have hgate := (continuous_gapCutoff gamma).comp hgap
  have h := (hgate.pow 2).mul ((continuous_weighted_norm N hN J gamma hg chi modes u hu f g).pow 2)
  convert h using 1
  ext x
  simp only [energy, QuarticGapTiltWeight.weight, SquaredGapTiltWeight.weight,
    localAmplitude, mul_pow, mul_assoc, Function.comp_def, Pi.mul_apply]

theorem integrable_energy (N : ℝ) (hN : 0 < N) (J : ℕ)
    (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (f g : Field) :
    Integrable (energy N hN J gamma chi modes u f g) :=
  (continuous_energy N hN J gamma hg chi modes u hu f g).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end Mettapedia.FluidDynamics.NavierStokes.PressureMovingDirectionEnergy
