import Mettapedia.Computability.PNP.PostSwitchRandomizedResidualObstruction

/-!
# PNP randomized-residual anchors: post-switch finite-coin residuals

Exact post-switch finite-coin randomized-residual anchors over the invariant projection surface.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: on the exact post-switch surface, supportwise-
unresolved finite-coin randomized residuals cannot provide positive doubled
advantage over the invariant projection. -/
theorem randomizedResidualCoverage_anchor_postSwitch_supportwise_unresolved_no_positive_advantage
    {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hunresolved :
      ∀ u c, 0 < w u * coinWeight c → v (tiInputMap u) c = v u c) :
    ¬ 0 < doubledAdvantage
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h :=
  not_pos_doubledAdvantage_randomizedResidual_invariantProjection_of_supportwise_unresolved
    v y w coinWeight h hy hw hunresolved

/-- Route-coverage anchor: on the exact post-switch surface, exact-input-
invariant support blocks strict half-accuracy finite-coin randomized-residual
advantage over the invariant projection. -/
theorem randomizedResidualCoverage_anchor_postSwitch_exact_support_no_strict_half_advantage
    {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hsupport : exactInputInvariantWeightedSupport w) :
    ¬ weightedTotalMass (productWeight w coinWeight) <
      2 * weightedCorrectMass
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h :=
  not_total_lt_two_mul_weightedCorrectMass_randomizedResidual_invariantProjection_of_exactInputInvariantWeightedSupport
    v y w coinWeight h hy hw hsupport

/-- Route-coverage anchor: on the exact post-switch surface, positive
finite-coin randomized-residual advantage must expose a positive joint-support
input/coin pair resolving the local-input switch. -/
theorem randomizedResidualCoverage_anchor_postSwitch_positive_advantage_witnesses_resolving_coin
    {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      0 < doubledAdvantage
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ u c, 0 < w u * coinWeight c ∧ v (tiInputMap u) c ≠ v u c :=
  exists_resolving_coin_of_pos_doubledAdvantage_randomizedResidual_invariantProjection
    v y w coinWeight h hy hw hadv

/-- Route-coverage anchor: on the exact post-switch surface, positive
finite-coin randomized-residual advantage is already witnessed by a
deterministic positive-weight coin slice with positive ordinary resolving
mass for the local-input switch. -/
theorem randomizedResidualCoverage_anchor_postSwitch_positive_advantage_witnesses_deterministic_coin_slice
    {Z Coin V : Type*} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      0 < doubledAdvantage
        (fun xr : PostSwitchInput Z k × Coin =>
          (invariantProjection xr.1, v xr.1 xr.2))
        (fun xr : PostSwitchInput Z k × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧
      0 < resolvedMass tiInputMap (fun u => v u c) w :=
  exists_positive_coin_resolvedMass_of_pos_doubledAdvantage_randomizedResidual_invariantProjection
    v y w coinWeight h hy hw hadv

/-- Route-coverage anchor: on the exact post-switch surface, strict half-
accuracy finite-coin randomized-residual advantage is already witnessed by a
deterministic positive-weight coin slice with positive ordinary resolving
mass for the local-input switch. -/
theorem randomizedResidualCoverage_anchor_postSwitch_strict_half_advantage_witnesses_deterministic_coin_slice
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
      0 < resolvedMass tiInputMap (fun u => v u c) w :=
  exists_positive_coin_resolvedMass_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual_invariantProjection
    v y w coinWeight h hy hw hadv

/-- Route-coverage anchor: on the exact post-switch surface, strict half-
accuracy finite-coin randomized-residual advantage already collapses to a
deterministic positive-weight coin slice carrying the ordinary invariant-
projection residual obstruction package. -/
theorem randomizedResidualCoverage_anchor_postSwitch_strict_half_advantage_coin_slice_forces_residual_obstruction_package
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
            (fun u => v u c) (v u c))) :=
  exists_positive_coin_obstruction_package_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual_invariantProjection
    v y w coinWeight h hy hw hadv

end Mettapedia.Computability.PNP
