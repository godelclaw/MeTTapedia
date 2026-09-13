import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ProjectionCutoffLimit
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteInviscidSupport
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredProjectionStrainWork

/-!
# Oversized normalization for an explicitly resolved finite Fourier field

The sharp filter is constructed from the input support and its sumset.
It preserves reality and has zero instantaneous subgrid force. The actual
signed work remainder still tends to vortex stretching as normalization
grows. No invariant finite-dimensional solution is claimed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ResolvedProjectionCutoffLimit

open scoped Topology
open Filter MeasureTheory
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeBlockReality PancakeFrequencyProjectorCommutator
open LocalLowDiffusionBudget LocalVorticityEighthMoment InfiniteFilteredEquation
open FiniteInviscidSupport FilteredProjectionSourceSplit FilteredProjectionStrainWork
open FilteredCoherentProjectionBudget ProjectionCutoffLimit

local notation "T3" => UnitAddTorus (Fin 3)

theorem fullSubgridWork_resolved_zero (δ κ : ℝ) (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) : fullSubgridWork δ κ (sharpFilter (resolvedModes P)) u = 0 := by
  have hz (x : T3) : fullVorticity (0 : FourierVelocity) x = 0 := by
    simpa only [sub_self] using CurlEigenfieldDefect.fullVorticity_sub u u
      (FourierFiniteSupport.summable_fourierMoment P u hs 1)
      (FourierFiniteSupport.summable_fourierMoment P u hs 1) x
  simp [fullSubgridWork, resolved_subgridForce_zero P u hs, hz]

theorem signedWorkRemainder_resolved_eq (ν : ℝ) (hν : 0 < ν) (R : ℝ)
    (P : Finset Wavevector) (u : FourierVelocity) (hs : ∀ q, q ∉ P → u q = 0)
    (hd : ∀ q, modeDot q (u q) = 0) (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    signedWorkRemainder ν R (resolvedModes P) (sharpFilter (resolvedModes P)) u =
      strainRemainder (FiniteBandProjectionAbsorption.regularization ν R)
        (FiniteBandProjectionAbsorption.normalization R) u := by
  rw [signedWorkRemainder_eq_strainWork ν R hν (resolvedModes P) _
    (fun q hq ↦ by simp [sharpFilter, hq]) 1 (norm_sharpFilter_le_one _)
    (sharpFilter_resolved_reality P) u (summable_outputFiber P u hs) hd hr,
    filtered_input_eq P u hs, fullSubgridWork_resolved_zero _ _ P u hs]
  simp only [strainRemainder, zero_sub, neg_div]

/-- This test lies inside the radius hypotheses of the actual filtered
energy inequality for every sufficiently large radius. -/
theorem exists_admissible_radius (P : Finset Wavevector) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ q ∈ resolvedModes P, ‖frequencyVec q‖ ≤ R := by
  refine ⟨∑ q ∈ resolvedModes P, ‖frequencyVec q‖, ?_⟩
  intro R hR q hq
  exact (Finset.single_le_sum (fun k _ ↦ norm_nonneg (frequencyVec k)) hq).trans hR

theorem tendsto_resolved_signedWorkRemainder (ν : ℝ) (hν : 0 < ν)
    (P : Finset Wavevector) (u : FourierVelocity) (hs : ∀ q, q ∉ P → u q = 0)
    (hd : ∀ q, modeDot q (u q) = 0) (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    Tendsto (fun R : ℝ ↦ signedWorkRemainder ν R (resolvedModes P) (sharpFilter (resolvedModes P)) u)
      atTop (𝓝 (stretching u)) := by
  simp_rw [signedWorkRemainder_resolved_eq ν hν _ P u hs hd hr]
  exact tendsto_strainRemainder ν hν u (FourierFiniteSupport.summable_fourierMoment P u hs 4) hd

/-- A positive stretching input rules out a decaying upper bound of this
shape. Positivity of stretching is an explicit, separate hypothesis. -/
theorem no_decaying_resolved_upper_bound (ν : ℝ) (hν : 0 < ν)
    (P : Finset Wavevector) (u : FourierVelocity) (hs : ∀ q, q ∉ P → u q = 0)
    (hd : ∀ q, modeDot q (u q) = 0) (hr : ∀ q, u (-q) = coefficientConjugate (u q))
    (hpos : 0 < stretching u) :
    ¬ ∃ C : ℝ, ∀ᶠ R : ℝ in atTop,
      signedWorkRemainder ν R (resolvedModes P) (sharpFilter (resolvedModes P)) u ≤
        C / FiniteBandProjectionAbsorption.normalization R := by
  rintro ⟨C, hC⟩
  have hle := le_of_tendsto_of_tendsto
    (tendsto_resolved_signedWorkRemainder ν hν P u hs hd hr)
    (tendsto_normalization.const_div_atTop C) hC
  exact (not_le_of_gt hpos) hle

end Mettapedia.FluidDynamics.NavierStokes.ResolvedProjectionCutoffLimit
