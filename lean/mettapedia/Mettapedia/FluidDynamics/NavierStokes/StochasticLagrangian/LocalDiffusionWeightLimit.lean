import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralDiffusionWeightLimit
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalDepletedDiffusionBudget

/-!
# Actual diffusion cost without auxiliary smoothing

Spatial and temporal dominated convergence retain the capped defect/gap
weight. The dominating cost is continuous on each local existence window;
this is not a scale-uniform or maximal-time bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalDiffusionWeightLimit

open scoped Topology
open Filter MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeFourierStrainGradient PancakeMeasurableMaterialRate
open LocalAlignmentContinuity LocalDepletedDiffusionBudget
open SpectralAnisotropyLimit SpectralDiffusionWeight SpectralDiffusionWeightLimit
open LocalLowDiffusionBudget PancakeGalerkinKineticEnergy PancakeFourierMaterialPaths
open PancakeFilteredStrainDynamics
open LocalStrainGradientDensity LocalSpatialSpectralBounds

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def limitingDiffusionCost (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3) : ℝ :=
  (16 * nu / delta) * strainGradientSquare chi modes u x *
    limitingWeight (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x)

def coarseDiffusionCost (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3) : ℝ :=
  (16 * nu / delta) * (3 * strainGradientAmplitude modes chi u ^ 2) * ‖fullVorticity u x‖ ^ 2

theorem limitingDiffusionCost_eq_zero_of_aligned (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta nu c : ℝ) (x : T3)
    (hg : 0 < PancakeSpectralProjectorRegularity.SymmetricStrain.topGap
      (spatialStrain modes (filteredVelocity chi u) x))
    (hw : fullVorticity u x = c • PancakeSpectralFiniteDifference.topVector
      (spatialStrain modes (filteredVelocity chi u) x)) :
    limitingDiffusionCost chi modes u delta nu x = 0 := by
  rw [limitingDiffusionCost, hw, limitingWeight_aligned _ c hg, mul_zero]

theorem norm_limitingDiffusionCost_le_absolute (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (x : T3) :
    ‖limitingDiffusionCost chi modes u delta nu x‖ ≤
      |16 * nu / delta| * (3 * strainGradientAmplitude modes chi u ^ 2) * ‖fullVorticity u x‖ ^ 2 := by
  simp only [limitingDiffusionCost, norm_mul, Real.norm_of_nonneg (strainGradientSquare_nonneg chi modes u x),
    Real.norm_of_nonneg (limitingWeight_nonneg _ _), Real.norm_eq_abs]
  gcongr
  · exact limitingWeight_nonneg _ _
  · exact strainGradientSquare_le_amplitude chi modes u x
  · exact limitingWeight_le_norm_sq _ _

theorem norm_diffusionCost_le_absolute (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta epsilon nu : ℝ) (heps : 0 < epsilon) (x : T3) :
    ‖diffusionCost chi modes u delta epsilon nu x‖ ≤
      |16 * nu / delta| * (3 * strainGradientAmplitude modes chi u ^ 2) * ‖fullVorticity u x‖ ^ 2 := by
  simp only [diffusionCost, norm_mul, Real.norm_of_nonneg (strainGradientSquare_nonneg chi modes u x),
    Real.norm_of_nonneg (weight_nonneg _ _ epsilon heps), Real.norm_eq_abs]
  gcongr
  · exact weight_nonneg _ _ epsilon heps
  · exact strainGradientSquare_le_amplitude chi modes u x
  · exact weight_le_norm_sq _ _ _

theorem integrable_limitingDiffusionCost (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (delta nu : ℝ) :
    Integrable (limitingDiffusionCost chi modes u delta nu) := by
  have hw := continuous_fullVorticity u hu
  have hS := PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u)
  have hI : Integrable (fun x ↦ |16 * nu / delta| * (3 * strainGradientAmplitude modes chi u ^ 2) *
      ‖fullVorticity u x‖ ^ 2) :=
    (((hw.norm.pow 2).const_mul _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  apply hI.mono' (((continuous_strainGradientSquare chi modes u).const_mul _).measurable.mul
    (measurable_limitingWeight _ _ hS hw)).aestronglyMeasurable
  exact Eventually.of_forall (norm_limitingDiffusionCost_le_absolute chi modes u delta nu)

theorem norm_limitingDiffusionCost_le (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu) (x : T3) :
    ‖limitingDiffusionCost chi modes u delta nu x‖ ≤ coarseDiffusionCost chi modes u delta nu x := by
  simpa only [coarseDiffusionCost, abs_of_nonneg (by positivity : 0 ≤ 16 * nu / delta)] using
    norm_limitingDiffusionCost_le_absolute chi modes u delta nu x

theorem continuous_coarseDiffusionCost (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (delta nu : ℝ) :
    Continuous (coarseDiffusionCost chi modes u delta nu) :=
  ((LocalLowDiffusionBudget.continuous_fullVorticity u hu).norm.pow 2).const_mul _

theorem continuous_coarseDiffusionCost_spaceTime {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (g : Wavevector → ℝ) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (delta : ℝ) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      coarseDiffusionCost chi modes (s.coefficients z.1) delta nu z.2) := by
  have hc (q : Wavevector) (i : Fin 3) :
      Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q i) :=
    (s.continuous q i).comp continuous_subtype_val
  have hA : Continuous (fun t : Set.Icc (0 : ℝ) T ↦ strainGradientAmplitude modes chi (s.coefficients t)) := by
    unfold strainGradientAmplitude
    exact continuous_finsetSum modes (fun q _ ↦ continuous_const.mul
      (((PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℂ)).comp (continuous_pi (fun i ↦ hc q i))).norm))
  exact (continuous_const.mul (continuous_const.mul ((hA.comp continuous_fst).pow 2))).mul
    ((continuous_fullVorticity_spaceTime s g hSum hu).norm.pow 2)

theorem tendsto_integral_diffusionCost (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (delta nu : ℝ) :
    Tendsto (fun n ↦ ∫ x : T3, diffusionCost chi modes u delta (approximationParameter n) nu x)
      atTop (𝓝 (∫ x : T3, limitingDiffusionCost chi modes u delta nu x)) := by
  have hw := LocalLowDiffusionBudget.continuous_fullVorticity u hu
  apply tendsto_integral_of_dominated_convergence
    (fun x ↦ |16 * nu / delta| * (3 * strainGradientAmplitude modes chi u ^ 2) * ‖fullVorticity u x‖ ^ 2)
  · exact fun n ↦ (continuous_diffusionCost chi modes u hu delta _ nu
      (approximationParameter_pos n)).measurable.aestronglyMeasurable
  · exact ((hw.norm.pow 2).const_mul _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact fun n ↦ Eventually.of_forall (norm_diffusionCost_le_absolute chi modes u delta _ nu
      (approximationParameter_pos n))
  · exact Eventually.of_forall (fun x ↦
      (tendsto_weight (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x)
        approximationParameter (Eventually.of_forall approximationParameter_pos) tendsto_approximationParameter).const_mul
          ((16 * nu / delta) * strainGradientSquare chi modes u x))

theorem intervalIntegrable_and_tendsto_integral_cost {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 ≤ nu)
    (g : Wavevector → ℝ) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (delta : ℝ) (hd : 0 < delta)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ ∫ x : T3,
      limitingDiffusionCost chi modes (s.coefficients τ) delta nu x) volume 0 t ∧
    Tendsto (fun n ↦ ∫ τ in (0 : ℝ)..t, ∫ x : T3,
      diffusionCost chi modes (s.coefficients τ) delta (approximationParameter n) nu x)
      atTop (𝓝 (∫ τ in (0 : ℝ)..t, ∫ x : T3,
        limitingDiffusionCost chi modes (s.coefficients τ) delta nu x)) := by
  let F := fun n τ ↦ ∫ x : T3,
    diffusionCost chi modes (s.coefficients τ) delta (approximationParameter n) nu x
  let f := fun τ ↦ ∫ x : T3, limitingDiffusionCost chi modes (s.coefficients τ) delta nu x
  let bound := fun τ ↦ ∫ x : T3, coarseDiffusionCost chi modes (s.coefficients τ) delta nu x
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hu1 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) t) : Summable (fourierMoment 1 (s.coefficients τ)) :=
    summable_fourierMoment_of_le _ (by omega : 1 ≤ 2)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub hτ)))
  have hBx (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) t) :
      Integrable (coarseDiffusionCost chi modes (s.coefficients τ) delta nu) :=
    (continuous_coarseDiffusionCost chi modes _ (hu1 τ hτ) delta nu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB : IntervalIntegrable bound volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_spatialIntegral _
      (continuous_coarseDiffusionCost_spaceTime s g hSum hu chi modes delta)).mono hsub)
  have hF (n : ℕ) : IntervalIntegrable (F n) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_spatialIntegral _
      (continuous_diffusionCost_spaceTime s g hSum hu chi modes delta
        (approximationParameter n) (approximationParameter_pos n))).mono hsub)
  have hlim (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) t) : Tendsto (fun n ↦ F n τ) atTop (𝓝 (f τ)) :=
    tendsto_integral_diffusionCost chi modes _ (hu1 τ hτ) delta nu
  have hbound (n : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) t) : ‖F n τ‖ ≤ bound τ := by
    apply norm_integral_le_of_norm_le (hBx τ hτ)
    exact Eventually.of_forall (fun x ↦ by
      rw [Real.norm_of_nonneg (diffusionCost_nonneg chi modes _ delta _ nu hd (approximationParameter_pos n) hnu x)]
      exact diffusionCost_le_coarse chi modes _ delta _ nu hd hnu x)
  have hfbound (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) t) : ‖f τ‖ ≤ bound τ :=
    norm_integral_le_of_norm_le (hBx τ hτ)
      (Eventually.of_forall (norm_limitingDiffusionCost_le chi modes _ delta nu hd hnu))
  have hmem : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) t := by
    rw [Set.uIoc_of_le ht.1]
    exact Set.Ioc_subset_Icc_self
  have hm : AEStronglyMeasurable f (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n ↦ (hF n).def'.1) (by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with τ hτ
      exact hlim τ (hmem hτ))
  refine ⟨hB.mono_fun' hm ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with τ hτ
    exact hfbound τ (hmem hτ)
  · exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
      (Eventually.of_forall (fun n ↦ (hF n).def'.1))
      (Eventually.of_forall (fun n ↦ Eventually.of_forall (fun τ hτ ↦ hbound n τ (hmem hτ)))) hB
      (Eventually.of_forall (fun τ hτ ↦ hlim τ (hmem hτ)))

end Mettapedia.FluidDynamics.NavierStokes.LocalDiffusionWeightLimit
