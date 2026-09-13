import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PositiveStretchingMean
import Mettapedia.Analysis.WeightedProjectionVariationTests

/-!
# Cutoff-limit regressions

Zero vorticity has zero first variation. Parallel fields have zero
limiting stretching, whereas the explicit three-wave field has a
strictly positive limit even with zero instantaneous subgrid force.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ProjectionCutoffLimitTests

open scoped Topology
open Mettapedia.Analysis PeriodicFourierTriad
open ProjectionCutoffLimit FiniteBandProjectionAbsorption
open LocalVorticityEighthMoment ParallelHeatFlow LocalLowDiffusionBudget
open PancakeFrequencyProjectorCommutator InfiniteFilteredEquation FiniteInviscidSupport

theorem zero_first_variation (δ : ℝ) (b v z : EuclideanSpace ℝ (Fin 3)) :
    WeightedProjectionParabolic.weightedRate δ 0 b v z = 0 :=
  WeightedProjectionVariationTests.zero_field_rate δ b v z

theorem parallel_strainRemainder_limit (ν : ℝ) (hν : 0 < ν)
    (a : Wavevector →₀ ℂ) (ha : IsHorizontal a) :
    Filter.Tendsto (fun R : ℝ ↦ strainRemainder (regularization ν R) (normalization R)
      (fun q ↦ vertical (a q))) Filter.atTop (𝓝 0) := by
  simpa only [stretching_eq_zero a ha] using tendsto_strainRemainder ν hν
    (fun q ↦ vertical (a q)) (summable_initial_fourierMoment 4 a) (transverse ha)

theorem positive_snapshot_resolved_force_zero :
    subgridForce (sharpFilter (resolvedModes PositiveStretchingSnapshot.modes))
      PositiveStretchingSnapshot.coefficients = 0 :=
  resolved_subgridForce_zero _ _ PositiveStretchingSnapshot.supported

theorem positive_snapshot_limit (ν : ℝ) (hν : 0 < ν) :
    Filter.Tendsto (fun R : ℝ ↦ FilteredCoherentProjectionBudget.signedWorkRemainder ν R
      (resolvedModes PositiveStretchingSnapshot.modes)
      (sharpFilter (resolvedModes PositiveStretchingSnapshot.modes))
      PositiveStretchingSnapshot.coefficients) Filter.atTop
        (𝓝 ((2 * Real.pi) ^ 9 * PositiveStretchingSnapshot.stretchingPolynomial 0)) := by
  rw [← PositiveStretchingSnapshot.stretching_eq_zeroCoefficient]
  exact ResolvedProjectionCutoffLimit.tendsto_resolved_signedWorkRemainder ν hν _ _
    PositiveStretchingSnapshot.supported PositiveStretchingSnapshot.transverse
    PositiveStretchingSnapshot.reality

end Mettapedia.FluidDynamics.NavierStokes.ProjectionCutoffLimitTests
