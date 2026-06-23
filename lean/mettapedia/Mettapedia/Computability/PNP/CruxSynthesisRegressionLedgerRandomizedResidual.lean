import Mettapedia.Computability.PNP.CruxRandomizedResidualSubrepairLedger
import Mettapedia.Computability.PNP.CruxRandomizedResidualCoverageV13
import Mettapedia.Computability.PNP.CruxRandomizedResidualCoverageBroad
import Mettapedia.Computability.PNP.CruxRandomizedResidualAnchorsSymmetry
import Mettapedia.Computability.PNP.CruxRandomizedResidualAnchorsPostSwitchFork
import Mettapedia.Computability.PNP.CruxRandomizedResidualAnchorsFiniteCoin
import Mettapedia.Computability.PNP.CruxRandomizedResidualAnchorsPostSwitchFiniteCoin

/-!
# Regression checks for randomized-residual PNP crux ledger surfaces

Randomized-residual subrepair, deterministic-coin-slice, post-switch, and fork
package regressions extracted from the historical
`CruxSynthesisRegressionLedger` module.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem current_pnp_randomized_residual_covered_subrepairs_exact_regression
    (repair : PNPRandomizedResidualSubrepairClass) :
    repair ∈ currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact repair

theorem current_pnp_randomized_residual_deterministic_coin_slice_regression :
    PNPRandomizedResidualSubrepairClass.positiveAdvantageDeterministicCoinSliceWitness ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.positiveAdvantageDeterministicCoinSliceWitness

theorem current_pnp_randomized_residual_strict_half_deterministic_coin_slice_regression :
    PNPRandomizedResidualSubrepairClass.strictHalfDeterministicCoinSliceWitness ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.strictHalfDeterministicCoinSliceWitness

theorem current_pnp_randomized_residual_strict_half_coin_slice_residual_package_regression :
    PNPRandomizedResidualSubrepairClass.strictHalfDeterministicCoinSliceResidualObstructionPackage ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.strictHalfDeterministicCoinSliceResidualObstructionPackage

theorem current_pnp_post_switch_randomized_residual_deterministic_coin_slice_regression :
    PNPRandomizedResidualSubrepairClass.postSwitchPositiveAdvantageDeterministicCoinSliceWitness ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.postSwitchPositiveAdvantageDeterministicCoinSliceWitness

theorem current_pnp_post_switch_randomized_residual_strict_half_blocker_regression :
    PNPRandomizedResidualSubrepairClass.postSwitchExactSupportNoStrictHalfAdvantage ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.postSwitchExactSupportNoStrictHalfAdvantage

theorem current_pnp_post_switch_randomized_residual_strict_half_deterministic_coin_slice_regression :
    PNPRandomizedResidualSubrepairClass.postSwitchStrictHalfDeterministicCoinSliceWitness ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.postSwitchStrictHalfDeterministicCoinSliceWitness

theorem current_pnp_post_switch_randomized_residual_strict_half_coin_slice_residual_package_regression :
    PNPRandomizedResidualSubrepairClass.postSwitchStrictHalfDeterministicCoinSliceResidualObstructionPackage ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.postSwitchStrictHalfDeterministicCoinSliceResidualObstructionPackage

theorem current_pnp_post_switch_randomized_residual_supportwise_unresolved_subrepair_regression :
    PNPRandomizedResidualSubrepairClass.postSwitchSupportwiseUnresolvedNoAdvantage ∈
      currentPNPRandomizedResidualCoveredSubrepairs := by
  exact currentPNPRandomizedResidualCoveredSubrepairs_exact
    PNPRandomizedResidualSubrepairClass.postSwitchSupportwiseUnresolvedNoAdvantage

theorem v13_randomized_residual_subcoverage_regression :
    V13RandomizedResidualSubcoverage := by
  exact v13RandomizedResidualSubcoverage

theorem randomized_residual_strict_half_coin_slice_residual_package_regression
    {α Coin U V : Type*} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass (productWeight w coinWeight) <
        2 * weightedCorrectMass
          (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
          (fun xr : α × Coin => y xr.1)
          (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧
      (¬ SideInfoDeterminedBy u (fun x => v x c) ∧
        PositiveWeightSideInfoCollisionOverBase u (fun x => v x c) w ∧
        (∃ x, 0 < w x ∧ u (τ x) = u x ∧ v (τ x) c ≠ v x c) ∧
        (∃ x, 0 < w x ∧
          ¬ SourceOnlyPredicateCapturesSideEq u (fun x => v x c) (v x c))) := by
  exact
    randomizedResidualCoverage_anchor_strict_half_advantage_coin_slice_forces_residual_obstruction_package
      τ u v y w coinWeight h hτ hu hy hw hadv

theorem post_switch_randomized_residual_strict_half_coin_slice_residual_package_regression
    {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass (productWeight w coinWeight) <
        2 * weightedCorrectMass
          (fun xr : PostSwitchInput Z k × Coin =>
            (invariantProjection xr.1, v xr.1 xr.2))
          (fun xr : PostSwitchInput Z k × Coin => y xr.1)
          (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧
      (¬ SideInfoDeterminedBy invariantProjection (fun u => v u c) ∧
        PositiveWeightSideInfoCollisionOverBase invariantProjection
          (fun u => v u c) w ∧
        (∃ u, 0 < w u ∧
          invariantProjection (tiInputMap u) = invariantProjection u ∧
          v (tiInputMap u) c ≠ v u c) ∧
        (∃ u, 0 < w u ∧
          ¬ SourceOnlyPredicateCapturesSideEq invariantProjection
            (fun u => v u c) (v u c))) := by
  exact
    randomizedResidualCoverage_anchor_postSwitch_strict_half_advantage_coin_slice_forces_residual_obstruction_package
      v y w coinWeight h hy hw hadv

theorem post_switch_fork_strict_half_package_regression
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    (∃ u : PostSwitchInput Z k, 0 < w u ∧ (tiInputMap u).b ≠ u.b) ∧
      (∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a) ∧
      ¬ exactInputInvariantWeightedSupport w := by
  exact
    postSwitchForkCoverage_anchor_strict_half_advantage_fork_obstruction_package
      y w h hy hw hadv

end Mettapedia.Computability.PNP.CruxSynthesisRegression
