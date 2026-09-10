import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralTiltExcess
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSourceExcess
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalJointSourceTilt

/-!
# The actual alignment source after direct-tilt absorption

The complete symmetric nonviscous source is used before its transverse
action is measured. The scalar excess is bounded by the previous source
cost, is measurable through collisions, and retains the signed mismatch
and energy-regularizer terms. The weak spatial diffusion estimate is
applied directly to the physical material rate with this sharper source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeMeasurableMaterialRate PancakeFourierMaterialPaths
open PancakeFilteredStrainDynamics PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution PancakeRegularizedMaterialRate
open PancakePhysicalLaplacian LocalJointDiffusionBudget
open LocalAlignmentForcing LocalAlignmentContinuity LocalLimitingAlignmentSource
open LocalLowDiffusionBudget LocalJointSourceTilt LocalDepletedDiffusionBudget LocalDiffusionWeightLimit

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def sourceExcess (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  SpectralTiltExcess.excess (spatialStrain modes (filteredVelocity chi u) x)
    (nonviscousRemainder chi modes outputs u x) (fullVorticity u x)

def forcingEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) : ℝ :=
  sourceExcess chi modes outputs u x +
    2 * ⟪residual chi modes u x, strainMismatch chi modes u x⟫ +
    2 * delta * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫

theorem sourceExcess_nonneg (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : 0 ≤ sourceExcess chi modes outputs u x :=
  SpectralTiltExcess.excess_nonneg _ _ _

theorem sourceExcess_le_previous (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    sourceExcess chi modes outputs u x ≤ LocalSourceExcess.sourceExcess chi modes outputs u x :=
  SpectralTiltExcess.excess_le_previous _ _ _

theorem sourceExcess_le_coarse (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    sourceExcess chi modes outputs u x ≤ 2 * ‖nonviscousRemainder chi modes outputs u x‖ *
      ‖fullVorticity u x‖ ^ 2 := SpectralTiltExcess.excess_le_coarse _ _ _

theorem sourceExcess_le_jointTilt_cost (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    sourceExcess chi modes outputs u x ≤
      max (2 * ‖nonviscousRemainder chi modes outputs u x‖ - topGap S ^ 2 / 8) 0 *
        SpectralDiffusionWeightLimit.limitingWeight S (fullVorticity u x) +
      8 * (‖jointTilt chi modes outputs u x‖ / topGap S) ^ 2 * ‖fullVorticity u x‖ ^ 2 := by
  dsimp only
  rw [sourceExcess, SpectralTiltExcess.excess, if_pos hg]
  simpa only [SpectralTiltExcess.refinedCost, SpectralTiltExcess.tiltNorm_eq, jointTilt] using
    min_le_right (SpectralSourceExcess.excess (spatialStrain modes (filteredVelocity chi u) x)
      (nonviscousRemainder chi modes outputs u x) (fullVorticity u x))
      (SpectralTiltExcess.refinedCost (spatialStrain modes (filteredVelocity chi u) x)
        (nonviscousRemainder chi modes outputs u x) (fullVorticity u x))

theorem forcingEnvelope_le_previous (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) :
    forcingEnvelope chi modes outputs u delta x ≤ LocalSourceExcess.forcingEnvelope chi modes outputs u delta x := by
  have h := sourceExcess_le_previous chi modes outputs u x
  unfold forcingEnvelope LocalSourceExcess.forcingEnvelope
  linarith only [h]

theorem materialRate_add_threeQuarters_residual_le (chi : Wavevector → ℂ)
    (modes outputs : Finset Wavevector) (u : FourierVelocity) (delta nu : ℝ) (x : T3) :
    materialRate chi modes outputs u delta nu x + (3 / 4 : ℝ) * ‖residual chi modes u x‖ ^ 2 ≤
      nu * linearRate (spatialStrain modes (filteredVelocity chi u) x) delta (fullVorticity u x)
        (strainLaplacian modes (filteredVelocity chi u) x) (fullVorticityLaplacian u x) +
      forcingEnvelope chi modes outputs u delta x := by
  have hR := (le_abs_self (remainderAnisotropy (nonviscousRemainder chi modes outputs u x)
    (topVector (spatialStrain modes (filteredVelocity chi u) x)) (fullVorticity u x))).trans
      (SpectralTiltExcess.abs_anisotropy_le_quarter_residual_add_excess _ _
        (nonviscousRemainder_adjoint chi modes outputs u x) _)
  unfold materialRate
  rw [linearRate_viscous_split, LocalSignedAlignmentBudget.resolved_add_strainMismatch]
  unfold forcingEnvelope sourceExcess LocalAlignmentForcing.residual
  linarith only [hR]

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
  SpectralTiltExcess.measurable_excess _ _ _
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
  have he := SpectralTiltExcess.measurable_excess _ _ _
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

/-- Direct application of weak diffusion to the sharper physical rate.
This is not inferred by decreasing an upper bound in an older inequality. -/
theorem integral_materialRate_add_quarter_residual_le
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (delta nu : ℝ) (hd : 0 < delta) (hnu : 0 ≤ nu)
    (hF : Integrable (materialRate chi modes outputs u delta nu)) :
    (∫ x : T3, materialRate chi modes outputs u delta nu x) +
      (1 / 4 : ℝ) * (∫ x : T3, ‖residual chi modes u x‖ ^ 2) ≤
      (∫ x : T3, LocalExcessDiffusionEnergy.excessCost chi modes u delta nu x) +
        ∫ x : T3, forcingEnvelope chi modes outputs u delta x := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hz : Integrable (fun x : T3 ↦ ‖residual chi modes u x‖ ^ 2) :=
    ((continuous_residual chi modes u hu1).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR := integrable_forcingEnvelope chi modes outputs u hu1 delta
  have hlim := (tendsto_integral_diffusionCost chi modes u hu1 delta nu).add_const
    (∫ x : T3, forcingEnvelope chi modes outputs u delta x)
  have h : (∫ x : T3, materialRate chi modes outputs u delta nu x) +
      (3 / 4 : ℝ) * (∫ x : T3, ‖residual chi modes u x‖ ^ 2) ≤
      (∫ x : T3, limitingDiffusionCost chi modes u delta nu x) +
        ∫ x : T3, forcingEnvelope chi modes outputs u delta x :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim (fun n ↦ by
    have h := integral_laplacian_diffusion_local_paid modes chi u hu
      (fun x ↦ materialRate chi modes outputs u delta nu x + (3 / 4 : ℝ) * ‖residual chi modes u x‖ ^ 2)
      (forcingEnvelope chi modes outputs u delta) delta (SpectralAnisotropyLimit.approximationParameter n) nu
      hd (SpectralAnisotropyLimit.approximationParameter_pos n) hnu (hF.add (hz.const_mul (3 / 4 : ℝ))) hR
      (Eventually.of_forall (materialRate_add_threeQuarters_residual_le chi modes outputs u delta nu))
    rw [integral_add hF (hz.const_mul (3 / 4 : ℝ)), integral_const_mul] at h
    simpa only [diffusionCost, mul_assoc, integral_const_mul] using h)
  have hD := LocalExcessDiffusionEnergy.integral_limitingDiffusionCost_le_half_residual_add_excessCost
    chi modes u hu1 delta nu hd hnu
  linarith only [h, hD]

end Mettapedia.FluidDynamics.NavierStokes.LocalTiltSource
