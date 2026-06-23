import Mettapedia.Computability.PNP.CruxRandomizedResidualCoverageV13Spec

/-!
# PNP randomized-residual V13 subcoverage proofs

The theorem-backed V13 randomized-residual subcoverage is factored into named
finite-coin and exact-post-switch subcoverages.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

@[simp] theorem v13RandomizedResidualFiniteCoinBudgetCoverage :
    V13RandomizedResidualFiniteCoinBudgetCoverage := by
  refine ⟨?_, ?_, ?_⟩
  · intro α Coin U V _Fintypeα _FintypeCoin τ u v y w coinWeight h hτ hu hy hw
    exact
      doubledAdvantage_randomizedResidual_le_resolvedMass
        τ u v y w coinWeight h hτ hu hy hw
  · intro α Coin V _Fintypeα _FintypeCoin τ v w coinWeight hunresolved
    exact
      randomizedResidualResolvedMass_eq_zero_of_supportwise_unresolved
        τ v w coinWeight hunresolved
  · intro α Coin U V _Fintypeα _FintypeCoin τ u v y w coinWeight h hτ hu hy hw hunresolved
    exact
      randomizedResidualCoverage_anchor_supportwise_unresolved_no_positive_advantage
        τ u v y w coinWeight h hτ hu hy hw hunresolved

@[simp] theorem v13RandomizedResidualFiniteCoinWitnessCoverage :
    V13RandomizedResidualFiniteCoinWitnessCoverage := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α Coin U V _Fintypeα _FintypeCoin τ u v y w coinWeight h hτ hu hy hw hadv
    exact
      randomizedResidualCoverage_anchor_positive_advantage_witnesses_resolving_coin
        τ u v y w coinWeight h hτ hu hy hw hadv
  · intro α Coin U V _Fintypeα _FintypeCoin τ u v y w coinWeight h hτ hu hy hw hadv
    exact
      randomizedResidualCoverage_anchor_positive_advantage_witnesses_deterministic_coin_slice
        τ u v y w coinWeight h hτ hu hy hw hadv
  · intro α Coin U V _Fintypeα _FintypeCoin τ u v y w coinWeight h hτ hu hy hw hadv
    exact
      randomizedResidualCoverage_anchor_strict_half_advantage_witnesses_deterministic_coin_slice
        τ u v y w coinWeight h hτ hu hy hw hadv
  · intro α Coin U V _Fintypeα _FintypeCoin τ u v y w coinWeight h hτ hu hy hw hadv
    exact
      randomizedResidualCoverage_anchor_strict_half_advantage_coin_slice_forces_residual_obstruction_package
        τ u v y w coinWeight h hτ hu hy hw hadv

@[simp] theorem v13RandomizedResidualPostSwitchBlockerCoverage :
    V13RandomizedResidualPostSwitchBlockerCoverage := by
  refine ⟨?_, ?_⟩
  · intro Z Coin V k _FintypeZ _FintypeCoin v y w coinWeight h hy hw hunresolved
    exact
      randomizedResidualCoverage_anchor_postSwitch_supportwise_unresolved_no_positive_advantage
        v y w coinWeight h hy hw hunresolved
  · intro Z Coin V k _FintypeZ _FintypeCoin v y w coinWeight h hy hw hsupport
    exact
      randomizedResidualCoverage_anchor_postSwitch_exact_support_no_strict_half_advantage
        v y w coinWeight h hy hw hsupport

@[simp] theorem v13RandomizedResidualPostSwitchWitnessCoverage :
    V13RandomizedResidualPostSwitchWitnessCoverage := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z Coin V k _FintypeZ _FintypeCoin v y w coinWeight h hy hw hadv
    exact
      randomizedResidualCoverage_anchor_postSwitch_positive_advantage_witnesses_resolving_coin
        v y w coinWeight h hy hw hadv
  · intro Z Coin V k _FintypeZ _FintypeCoin v y w coinWeight h hy hw hadv
    exact
      randomizedResidualCoverage_anchor_postSwitch_positive_advantage_witnesses_deterministic_coin_slice
        v y w coinWeight h hy hw hadv
  · intro Z Coin V k _FintypeZ _FintypeCoin v y w coinWeight h hy hw hadv
    exact
      randomizedResidualCoverage_anchor_postSwitch_strict_half_advantage_witnesses_deterministic_coin_slice
        v y w coinWeight h hy hw hadv
  · intro Z Coin V k _FintypeZ _FintypeCoin v y w coinWeight h hy hw hadv
    exact
      randomizedResidualCoverage_anchor_postSwitch_strict_half_advantage_coin_slice_forces_residual_obstruction_package
        v y w coinWeight h hy hw hadv

@[simp] theorem v13RandomizedResidualSubcoverage :
    V13RandomizedResidualSubcoverage := by
  exact
    ⟨v13RandomizedResidualFiniteCoinBudgetCoverage,
      v13RandomizedResidualFiniteCoinWitnessCoverage,
      v13RandomizedResidualPostSwitchBlockerCoverage,
      v13RandomizedResidualPostSwitchWitnessCoverage⟩

end Mettapedia.Computability.PNP
