import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralAnisotropyLimit
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalDepletedAlignmentSource

/-!
# The measurable limiting source for actual full-vorticity alignment

The auxiliary source parameter is removed pointwise. A continuous absolute
majorant is independent of that parameter; it proves spatial integrability
and convergence of the spatial source integrals. The energy regularizer
and its signed stretching contribution remain fixed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalLimitingAlignmentSource

open scoped Topology RealInnerProductSpace
open Filter MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeMeasurableMaterialRate PancakeFourierMaterialPaths
open PancakeFilteredStrainDynamics
open LocalLowDiffusionBudget LocalAlignmentForcing LocalAlignmentContinuity
open LocalDepletedAlignmentSource SpectralAnisotropyLimit

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def limitingForcingEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) : ℝ :=
  limitingEnvelope (spatialStrain modes (filteredVelocity chi u) x)
    (nonviscousRemainder chi modes outputs u x) (fullVorticity u x) +
      2 * ⟪residual chi modes u x, strainMismatch chi modes u x⟫ +
      2 * delta * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫

def absoluteSourceBound (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) : ℝ :=
  2 * ‖nonviscousRemainder chi modes outputs u x‖ * ‖fullVorticity u x‖ ^ 2 +
    |2 * ⟪residual chi modes u x, strainMismatch chi modes u x⟫| +
    |2 * delta * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫|

private theorem abs_add_add_le_of_between (a b c C : ℝ) (ha : 0 ≤ a) (hC : a ≤ C) :
    |a + b + c| ≤ C + |b| + |c| := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  rw [abs_of_nonneg ha] at h1
  linarith

theorem norm_depletedForcingEnvelope_le (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta epsilon : ℝ) (x : T3) :
    ‖depletedForcingEnvelope chi modes outputs u delta epsilon x‖ ≤
      absoluteSourceBound chi modes outputs u delta x := by
  exact abs_add_add_le_of_between _ _ _ _ (SpectralAnisotropyEnvelope.envelope_nonneg _ _ _ _)
    (SpectralAnisotropyEnvelope.envelope_le_coarse _ _ _ _)

theorem norm_limitingForcingEnvelope_le (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) :
    ‖limitingForcingEnvelope chi modes outputs u delta x‖ ≤
      absoluteSourceBound chi modes outputs u delta x := by
  exact abs_add_add_le_of_between _ _ _ _ (limitingEnvelope_nonneg _ _ _) (limitingEnvelope_le_coarse _ _ _)

theorem tendsto_depletedForcingEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) :
    Tendsto (fun n ↦ depletedForcingEnvelope chi modes outputs u delta (approximationParameter n) x)
      atTop (𝓝 (limitingForcingEnvelope chi modes outputs u delta x)) := by
  have h := tendsto_envelope (spatialStrain modes (filteredVelocity chi u) x)
    (nonviscousRemainder chi modes outputs u x) (fullVorticity u x) approximationParameter
    (Eventually.of_forall approximationParameter_pos) tendsto_approximationParameter
  exact (h.add_const (2 * ⟪residual chi modes u x, strainMismatch chi modes u x⟫)).add_const
    (2 * delta * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫)

theorem continuous_absoluteSourceBound (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (delta : ℝ) :
    Continuous (absoluteSourceBound chi modes outputs u delta) := by
  have hw := continuous_fullVorticity u hu
  exact (((continuous_const.mul (continuous_nonviscousRemainder chi modes outputs u).norm).mul
    (hw.norm.pow 2)).add
    (continuous_const.mul ((continuous_residual chi modes u hu).inner
      (continuous_strainMismatch chi modes u hu))).abs).add
    (continuous_const.mul (hw.inner ((continuous_fullStrainOperator u hu).clm_apply hw))).abs

theorem measurable_limitingForcingEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (delta : ℝ) :
    Measurable (limitingForcingEnvelope chi modes outputs u delta) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n x ↦ depletedForcingEnvelope chi modes outputs u delta (approximationParameter n) x)
    (fun n ↦ (continuous_depletedForcingEnvelope chi modes outputs u hu delta
      (approximationParameter n) (approximationParameter_pos n)).measurable)
  exact tendsto_pi_nhds.mpr (tendsto_depletedForcingEnvelope chi modes outputs u delta)

theorem integrable_limitingForcingEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (delta : ℝ) :
    Integrable (limitingForcingEnvelope chi modes outputs u delta) :=
  ((continuous_absoluteSourceBound chi modes outputs u hu delta).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).mono'
    (measurable_limitingForcingEnvelope chi modes outputs u hu delta).aestronglyMeasurable
    (Eventually.of_forall (norm_limitingForcingEnvelope_le chi modes outputs u delta))

theorem tendsto_integral_depletedForcingEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (delta : ℝ) :
    Tendsto (fun n ↦ ∫ x : T3, depletedForcingEnvelope chi modes outputs u delta (approximationParameter n) x)
      atTop (𝓝 (∫ x : T3, limitingForcingEnvelope chi modes outputs u delta x)) := by
  exact tendsto_integral_of_dominated_convergence (absoluteSourceBound chi modes outputs u delta)
    (fun n ↦ (continuous_depletedForcingEnvelope chi modes outputs u hu delta
      (approximationParameter n) (approximationParameter_pos n)).aestronglyMeasurable)
    ((continuous_absoluteSourceBound chi modes outputs u hu delta).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (fun n ↦ Eventually.of_forall (norm_depletedForcingEnvelope_le chi modes outputs u delta (approximationParameter n)))
    (Eventually.of_forall (tendsto_depletedForcingEnvelope chi modes outputs u delta))

theorem continuous_absoluteSourceBound_spaceTime {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (delta : ℝ) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      absoluteSourceBound chi modes outputs (s.coefficients z.1) delta z.2) := by
  have hc (q : Wavevector) (i : Fin 3) :
      Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q i) :=
    (s.continuous q i).comp continuous_subtype_val
  have hw := continuous_fullVorticity_spaceTime s g hSum hu
  have hR := continuous_nonviscousRemainder_parametric _ hc g hg hSum (fun t ↦ hu t t.2)
    chi C hchi modes outputs
  have hS := continuous_fullStrainOperator_parametric _ hc g hSum (fun t ↦ hu t t.2)
  exact (((continuous_const.mul hR.norm).mul (hw.norm.pow 2)).add
    (continuous_const.mul ((continuous_residual_spaceTime s g hSum hu chi modes).inner
      (continuous_strainMismatch_spaceTime s g hSum hu chi modes))).abs).add
    (continuous_const.mul (hw.inner (hS.clm_apply hw))).abs

end Mettapedia.FluidDynamics.NavierStokes.LocalLimitingAlignmentSource
