import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralSourceExcess
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSourceCommutator
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalExcessDiffusionEnergy

/-!
# The integrable excess of the actual alignment source

The complete nonviscous remainder is used before taking its commutator.
A quarter of the coherent residual pays the absorbable source. The
remaining source retains the signed strain mismatch and energy-regularizer
terms. Spatial and time integrability hold through top-gap collisions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess

open scoped RealInnerProductSpace
open Filter MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeMeasurableMaterialRate PancakeFourierMaterialPaths
open PancakeFilteredStrainDynamics PancakeSpectralProjectorRegularity.SymmetricStrain
open LocalAlignmentForcing LocalAlignmentContinuity LocalLimitingAlignmentSource
open LocalLowDiffusionBudget LocalSourceCommutator

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def sourceExcess (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  SpectralSourceExcess.excess (spatialStrain modes (filteredVelocity chi u) x)
    (nonviscousRemainder chi modes outputs u x) (fullVorticity u x)

def forcingEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) : ℝ :=
  sourceExcess chi modes outputs u x +
    2 * ⟪residual chi modes u x, strainMismatch chi modes u x⟫ +
    2 * delta * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫

theorem sourceExcess_nonneg (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : 0 ≤ sourceExcess chi modes outputs u x :=
  SpectralSourceExcess.excess_nonneg _ _ _

theorem sourceExcess_le_coarse (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    sourceExcess chi modes outputs u x ≤ 2 * ‖nonviscousRemainder chi modes outputs u x‖ *
      ‖fullVorticity u x‖ ^ 2 := SpectralSourceExcess.excess_le_coarse _ _ _

theorem forcingEnvelope_le_previous (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) :
    forcingEnvelope chi modes outputs u delta x ≤ limitingForcingEnvelope chi modes outputs u delta x := by
  have h := SpectralSourceExcess.excess_le_envelope
    (spatialStrain modes (filteredVelocity chi u) x) (nonviscousRemainder chi modes outputs u x)
    (fullVorticity u x)
  unfold forcingEnvelope sourceExcess limitingForcingEnvelope
  linarith only [h]

theorem previous_le_quarter_residual_add_forcingEnvelope (chi : Wavevector → ℂ)
    (modes outputs : Finset Wavevector) (u : FourierVelocity) (delta : ℝ) (x : T3) :
    limitingForcingEnvelope chi modes outputs u delta x ≤
      ‖residual chi modes u x‖ ^ 2 / 4 + forcingEnvelope chi modes outputs u delta x := by
  have h := SpectralSourceExcess.envelope_le_quarter_residual_add_excess
    (spatialStrain modes (filteredVelocity chi u) x) (nonviscousRemainder chi modes outputs u x)
    (fullVorticity u x)
  change _ ≤ ‖residual chi modes u x‖ ^ 2 / 4 + sourceExcess chi modes outputs u x at h
  unfold limitingForcingEnvelope forcingEnvelope
  linarith only [h]

theorem sourceExcess_eq_zero_of_commuting (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x))
    (hc : sourceCommutator chi modes outputs u x = 0)
    (hR : 16 * ‖nonviscousRemainder chi modes outputs u x‖ ≤
      topGap (spatialStrain modes (filteredVelocity chi u) x) ^ 2) :
    sourceExcess chi modes outputs u x = 0 :=
  SpectralSourceExcess.excess_eq_zero_of_commutator_eq_zero _ _ _ hg hc hR

theorem norm_forcingEnvelope_le (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) :
    ‖forcingEnvelope chi modes outputs u delta x‖ ≤ absoluteSourceBound chi modes outputs u delta x := by
  have h1 := abs_add_le (sourceExcess chi modes outputs u x)
    (2 * ⟪residual chi modes u x, strainMismatch chi modes u x⟫)
  have h2 := abs_add_le
    (sourceExcess chi modes outputs u x + 2 * ⟪residual chi modes u x, strainMismatch chi modes u x⟫)
    (2 * delta * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫)
  rw [abs_of_nonneg (sourceExcess_nonneg chi modes outputs u x)] at h1
  change |forcingEnvelope chi modes outputs u delta x| ≤ _
  unfold forcingEnvelope absoluteSourceBound
  linarith only [h1, h2, sourceExcess_le_coarse chi modes outputs u x]

theorem measurable_sourceExcess (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Measurable (sourceExcess chi modes outputs u) :=
  SpectralSourceExcess.measurable_excess _ _ _
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
    (continuous_nonviscousRemainder chi modes outputs u) (continuous_fullVorticity u hu)

theorem measurable_forcingEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (delta : ℝ) :
    Measurable (forcingEnvelope chi modes outputs u delta) := by
  have hw := continuous_fullVorticity u hu
  exact ((measurable_sourceExcess chi modes outputs u hu).add
    (continuous_const.mul ((continuous_residual chi modes u hu).inner
      (continuous_strainMismatch chi modes u hu))).measurable).add
    (continuous_const.mul (hw.inner ((continuous_fullStrainOperator u hu).clm_apply hw))).measurable

theorem integrable_forcingEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (delta : ℝ) :
    Integrable (forcingEnvelope chi modes outputs u delta) :=
  ((continuous_absoluteSourceBound chi modes outputs u hu delta).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).mono'
    (measurable_forcingEnvelope chi modes outputs u hu delta).aestronglyMeasurable
    (Eventually.of_forall (norm_forcingEnvelope_le chi modes outputs u delta))

theorem measurable_forcingEnvelope_spaceTime {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (delta : ℝ) :
    Measurable (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      forcingEnvelope chi modes outputs (s.coefficients z.1) delta z.2) := by
  have hc (q : Wavevector) (i : Fin 3) :
      Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q i) :=
    (s.continuous q i).comp continuous_subtype_val
  have hw := continuous_fullVorticity_spaceTime s g hSum hu
  have hS := continuous_fullStrainOperator_parametric _ hc g hSum (fun t ↦ hu t t.2)
  have he := SpectralSourceExcess.measurable_excess _ _ _
    (continuous_parametric_strain modes chi (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t)
      (fun q _ i ↦ hc q i))
    (continuous_nonviscousRemainder_parametric _ hc g hg hSum (fun t ↦ hu t t.2)
      chi C hchi modes outputs) hw
  exact (he.add (continuous_const.mul ((continuous_residual_spaceTime s g hSum hu chi modes).inner
    (continuous_strainMismatch_spaceTime s g hSum hu chi modes))).measurable).add
    (continuous_const.mul (hw.inner (hS.clm_apply hw))).measurable

theorem intervalIntegrable_forcingEnvelope {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (delta : ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ ↦ ∫ x : T3,
      forcingEnvelope chi modes outputs (s.coefficients τ) delta x) volume 0 t := by
  have hm := (measurable_forcingEnvelope_spaceTime s g hg hSum hu chi C hchi modes outputs delta
    ).stronglyMeasurable.integral_prod_right' (ν := (volume : Measure T3))
  have hmr : AEStronglyMeasurable (fun τ ↦ ∫ x : T3,
      forcingEnvelope chi modes outputs (s.coefficients τ) delta x) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ((aemeasurable_restrict_iff_comap_subtype measurableSet_Icc).mpr hm.measurable.aemeasurable).aestronglyMeasurable
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hmem : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) t := by
    rw [Set.uIoc_of_le ht.1]
    exact Set.Ioc_subset_Icc_self
  have hbound : IntervalIntegrable (fun τ ↦ ∫ x : T3,
      absoluteSourceBound chi modes outputs (s.coefficients τ) delta x) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_spatialIntegral _
      (continuous_absoluteSourceBound_spaceTime s g hg hSum hu chi C hchi modes outputs delta)).mono hsub)
  apply hbound.mono_fun' (hmr.mono_measure (Measure.restrict_mono (hmem.trans hsub) le_rfl))
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with τ hτ
  have hu1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 2)
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub (hmem hτ))))
  exact norm_integral_le_of_norm_le
    ((continuous_absoluteSourceBound chi modes outputs _ hu1 delta).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (Eventually.of_forall (norm_forcingEnvelope_le chi modes outputs _ delta))

theorem integral_previous_le_quarter_residual_add_forcingEnvelope
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (delta : ℝ) :
    (∫ x : T3, limitingForcingEnvelope chi modes outputs u delta x) ≤
      (1 / 4 : ℝ) * (∫ x : T3, ‖residual chi modes u x‖ ^ 2) +
        ∫ x : T3, forcingEnvelope chi modes outputs u delta x := by
  have hr : Integrable (fun x : T3 ↦ ‖residual chi modes u x‖ ^ 2) :=
    ((continuous_residual chi modes u hu).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he := integrable_forcingEnvelope chi modes outputs u hu delta
  have h := integral_mono (integrable_limitingForcingEnvelope chi modes outputs u hu delta)
    ((hr.const_mul (1 / 4 : ℝ)).add he) (fun x ↦ by
      simpa only [Pi.add_apply, div_eq_mul_inv, one_div, one_mul, mul_comm] using
        previous_le_quarter_residual_add_forcingEnvelope chi modes outputs u delta x)
  change (∫ x : T3, limitingForcingEnvelope chi modes outputs u delta x) ≤
    ∫ x : T3, (1 / 4 : ℝ) * ‖residual chi modes u x‖ ^ 2 + forcingEnvelope chi modes outputs u delta x at h
  rw [integral_add (hr.const_mul (1 / 4 : ℝ)) he, integral_const_mul] at h
  exact h

theorem integral_source_le_quarter_residual_add_excess {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (delta : ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ τ in (0 : ℝ)..t, ∫ x : T3, limitingForcingEnvelope chi modes outputs (s.coefficients τ) delta x) ≤
      (1 / 4 : ℝ) * (∫ τ in (0 : ℝ)..t, ∫ x : T3, ‖residual chi modes (s.coefficients τ) x‖ ^ 2) +
        ∫ τ in (0 : ℝ)..t, ∫ x : T3, forcingEnvelope chi modes outputs (s.coefficients τ) delta x := by
  have hr := LocalAlignmentContinuity.intervalIntegrable_residual_sq s g hSum hu chi modes t ht
  have he := intervalIntegrable_forcingEnvelope s g hg hSum hu chi C hchi modes outputs delta t ht
  have hp := (LocalAlignmentSourceLimit.intervalIntegrable_and_tendsto_integral_source
    s g hg hSum hu chi C hchi modes outputs delta t ht).1
  have h := intervalIntegral.integral_mono_on ht.1 hp ((hr.const_mul (1 / 4 : ℝ)).add he)
    (fun τ hτ ↦ integral_previous_le_quarter_residual_add_forcingEnvelope chi modes outputs _
      (summable_fourierMoment_of_le _ (by omega : 1 ≤ 2)
        (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ ⟨hτ.1, hτ.2.trans ht.2⟩))) delta)
  simpa only [intervalIntegral.integral_add (hr.const_mul (1 / 4 : ℝ)) he,
    intervalIntegral.integral_const_mul] using h

end Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess
