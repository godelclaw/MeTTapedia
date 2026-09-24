import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredAngularSourceBalance
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalProjectionInviscidWork
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PositiveStretchingMean

/-!
# Nonvanishing inviscid work under oversized angular normalization

The explicit angular gradient transfers source derivatives, but does not
make nonlinear work vanish as the correction coefficient tends to zero.
For a finite field, a constructed filter retains its entire instantaneous
nonlinear RHS. Its angular corrected work tends to actual vortex stretching.
The positive three-wave snapshot rules out a decaying upper bound of this
shape. This is not a blowup example or a refutation of a signed time budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.AngularInviscidWorkLimit

open scoped Topology RealInnerProductSpace
open Filter MeasureTheory
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCoefficientLimitEquation
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticityEighthMoment
open FourierFiniteSupport FiniteInviscidSupport InfiniteFilteredEquation
open FiniteAngularCurlVariation FilteredAngularMean FilteredAngularViscousBalance
open FiniteAngularSourceWork PancakeBlockReality FilteredAngularSourceBalance
open PancakeFrequencyProjectorCommutator

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def inviscidAngularVariation (u : FourierVelocity) : ℝ :=
  ∫ x : T3, FiniteAngularCurlVariation.densityRate u (infiniteVelocityRHS 0 u) x

/-- The ordinary octic energy source, extracted from the existing
unforced material/transport identity with zero correction coefficient. -/
theorem integral_octicInviscidWork_eq (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∫ x : T3, ‖fullVorticity u x‖ ^ 6 *
      ⟪fullVorticity u x, fullVorticity (infiniteVelocityRHS 0 u) x⟫) = stretching u := by
  have h := LocalProjectionInviscidWork.integral_correctedGradient_inviscidRHS 1 0
    (by norm_num) u (summable_fourierMoment P u hs 5) hd hr
  simpa only [LocalProjectionSourceWork.correctedGradient, div_zero, zero_smul,
    sub_zero, real_inner_smul_left, zero_mul] using h

theorem resolved_work_eq (κ : ℝ) (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    work κ (resolvedModes P) u (infiniteVelocityRHS 0 u) =
      stretching u - (3 / κ) * inviscidAngularVariation u := by
  have hv : ∀ q, q ∉ resolvedModes P → infiniteVelocityRHS 0 u q = 0 :=
    fun q hq ↦ inviscidRHS_eq_zero_off_sumset P u hs q
      (fun hp ↦ hq (sumset_subset_resolvedModes P hp))
  have ha := continuous_fullVorticity u (summable_fourierMoment P u hs 1)
  have hb := continuous_fullVorticity _ (summable_fourierMoment (resolvedModes P) _ hv 1)
  have hA : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 *
      ⟪fullVorticity u x, fullVorticity (infiniteVelocityRHS 0 u) x⟫) :=
    ((ha.norm.pow 6).mul (ha.inner hb)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hK : Integrable (FiniteAngularCurlVariation.densityRate u (infiniteVelocityRHS 0 u)) :=
    (Mettapedia.Analysis.AngularCurlDecomposition.continuous_angularCurlDensityRate _ _ _ _ ha hb
      (LocalSquaredGapGradient.continuous_fullCurlGradient u)
      (LocalSquaredGapGradient.continuous_fullCurlGradient _)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  unfold work meanWork
  rw [FilteredProjectionMean.restrictVelocity_eq_self (resolvedModes P) _ hv]
  unfold FiniteAngularCurlVariation.correctedDensityRate
  rw [integral_sub hA (hK.const_mul _), integral_const_mul, integral_octicInviscidWork_eq P u hs hd hr]
  rfl

theorem tendsto_resolved_work (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    Tendsto (fun κ : ℝ ↦ work κ (resolvedModes P) u (infiniteVelocityRHS 0 u)) atTop (𝓝 (stretching u)) := by
  simp_rw [resolved_work_eq _ P u hs hd hr]
  have hz := (tendsto_id.const_div_atTop (3 : ℝ)).mul_const (inviscidAngularVariation u)
  simpa only [id_eq, zero_mul, sub_zero] using tendsto_const_nhds.sub hz

theorem no_decaying_work_bound (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (hpos : 0 < stretching u) :
    ¬ ∃ C : ℝ, ∀ᶠ κ : ℝ in atTop,
      work κ (resolvedModes P) u (infiniteVelocityRHS 0 u) ≤ C / κ := by
  rintro ⟨C, hC⟩
  have hle := le_of_tendsto_of_tendsto (tendsto_resolved_work P u hs hd hr)
    (tendsto_id.const_div_atTop C) hC
  exact (not_le_of_gt hpos) hle

theorem positive_snapshot_no_decaying_work_bound :
    ¬ ∃ C : ℝ, ∀ᶠ κ : ℝ in atTop,
      work κ (resolvedModes PositiveStretchingSnapshot.modes) PositiveStretchingSnapshot.coefficients
        (infiniteVelocityRHS 0 PositiveStretchingSnapshot.coefficients) ≤ C / κ :=
  no_decaying_work_bound _ _ PositiveStretchingSnapshot.supported PositiveStretchingSnapshot.transverse
    PositiveStretchingSnapshot.reality PositiveStretchingSnapshot.stretching_pos

/-- The same work is the complete source of the constructed resolved
filter, not just one term with an omitted subgrid interaction. -/
theorem sourceWork_resolved_eq (κ : ℝ) (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    sourceWork κ (sharpFilter (resolvedModes P)) u =
      work κ (resolvedModes P) u (infiniteVelocityRHS 0 u) := by
  have hu : ∀ q, q ∉ resolvedModes P → u q = 0 :=
    fun q hq ↦ hs q (fun hp ↦ hq (subset_resolvedModes P hp))
  have hv : ∀ q, q ∉ resolvedModes P → infiniteVelocityRHS 0 u q = 0 :=
    fun q hq ↦ inviscidRHS_eq_zero_off_sumset P u hs q
      (fun hp ↦ hq (sumset_subset_resolvedModes P hp))
  rw [work_eq_pairing κ (resolvedModes P) u _ hu,
    FilteredProjectionMean.restrictVelocity_eq_self _ _ hv]
  unfold sourceWork
  rw [filtered_input_eq P u hs, filtered_inviscidRHS_eq P u hs]

theorem positive_snapshot_no_decaying_sourceWork_bound :
    ¬ ∃ C : ℝ, ∀ᶠ κ : ℝ in atTop,
      sourceWork κ (sharpFilter (resolvedModes PositiveStretchingSnapshot.modes))
        PositiveStretchingSnapshot.coefficients ≤ C / κ := by
  simp_rw [sourceWork_resolved_eq _ _ _ PositiveStretchingSnapshot.supported]
  exact positive_snapshot_no_decaying_work_bound

/-- Positive source work occurs beyond every coercive/dissipative
normalization threshold for a support-admissible fixed radius. -/
theorem positive_snapshot_beyond_every_threshold :
    ∃ R : ℝ, (∀ q ∈ resolvedModes PositiveStretchingSnapshot.modes, ‖frequencyVec q‖ ≤ R) ∧
      ∀ L : ℝ, ∃ κ : ℝ, 0 < κ ∧ L * (2 * Real.pi * R) ^ 2 ≤ κ ∧
        0 < sourceWork κ (sharpFilter (resolvedModes PositiveStretchingSnapshot.modes))
          PositiveStretchingSnapshot.coefficients := by
  obtain ⟨R, hR⟩ := ResolvedProjectionCutoffLimit.exists_admissible_radius PositiveStretchingSnapshot.modes
  refine ⟨R, hR R le_rfl, fun L ↦ ?_⟩
  have hpos := (tendsto_resolved_work _ _ PositiveStretchingSnapshot.supported
    PositiveStretchingSnapshot.transverse PositiveStretchingSnapshot.reality).eventually
      (eventually_gt_nhds PositiveStretchingSnapshot.stretching_pos)
  have hex := ((hpos.and (eventually_gt_atTop (0 : ℝ))).and
    (eventually_ge_atTop (L * (2 * Real.pi * R) ^ 2))).exists
  obtain ⟨κ, ⟨hp, hk⟩, hscale⟩ := hex
  refine ⟨κ, hk, hscale, ?_⟩
  rwa [sourceWork_resolved_eq _ _ _ PositiveStretchingSnapshot.supported]

end Mettapedia.FluidDynamics.NavierStokes.AngularInviscidWorkLimit
