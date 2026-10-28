import Mettapedia.Computability.PNP.CruxRandomizedResidualAnchorsFiniteCoin
import Mettapedia.Computability.PNP.CruxRandomizedResidualAnchorsPostSwitchFiniteCoin

/-!
# PNP broad randomized-residual coverage

The broad randomized-residual coverage package over finite-coin residuals and exact post-switch residuals.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- The broad randomized-residual repair class is covered in the precise
theorem-backed sense that finite-coin randomized residuals stay under the
ordinary resolving-mass budget, supportwise-unresolved randomized residuals
have zero joint resolving mass and hence no positive doubled advantage, any
surviving positive advantage already yields a deterministic positive-weight coin
slice with positive ordinary resolving mass, and any strict half-accuracy
advantage already collapses to an ordinary residual-side-information
obstruction package on such a deterministic slice.  The exact post-switch
specialization inherits the same supportwise-unresolved blocker, the
exact-support strict-half blocker, and the same coin-slice collapse to an
ordinary invariant-projection residual obstruction package. -/
def RandomizedResidualCoverage : Prop :=
  (∀ {α Coin U V : Type} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool),
      Function.Involutive τ →
        (∀ x, u (τ x) = u x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              doubledAdvantage
                  (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
                  (fun xr : α × Coin => y xr.1)
                  (productWeight w coinWeight) h
                ≤ randomizedResidualResolvedMass τ v w coinWeight) ∧
  (∀ {α Coin V : Type} [Fintype α] [Fintype Coin]
    (τ : α → α) (v : α → Coin → V)
    (w : α → ℕ) (coinWeight : Coin → ℕ),
      (∀ x c, 0 < w x * coinWeight c → v (τ x) c = v x c) →
        randomizedResidualResolvedMass τ v w coinWeight = 0) ∧
  (∀ {α Coin U V : Type} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool),
      Function.Involutive τ →
        (∀ x, u (τ x) = u x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              (∀ x c, 0 < w x * coinWeight c → v (τ x) c = v x c) →
                ¬ 0 < doubledAdvantage
                    (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
                    (fun xr : α × Coin => y xr.1)
                    (productWeight w coinWeight) h) ∧
  (∀ {α Coin U V : Type} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool),
      Function.Involutive τ →
        (∀ x, u (τ x) = u x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage
                  (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
                  (fun xr : α × Coin => y xr.1)
                  (productWeight w coinWeight) h →
                ∃ c, 0 < coinWeight c ∧
                  0 < resolvedMass τ (fun x => v x c) w) ∧
  (∀ {α Coin U V : Type} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool),
      Function.Involutive τ →
        (∀ x, u (τ x) = u x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              weightedTotalMass (productWeight w coinWeight) <
                2 * weightedCorrectMass
                  (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
                  (fun xr : α × Coin => y xr.1)
                  (productWeight w coinWeight) h →
                ∃ c, 0 < coinWeight c ∧
                  (¬ SideInfoDeterminedBy u (fun x => v x c) ∧
                    PositiveWeightSideInfoCollisionOverBase u
                      (fun x => v x c) w ∧
                    (∃ x, 0 < w x ∧ u (τ x) = u x ∧ v (τ x) c ≠ v x c) ∧
                    (∃ x, 0 < w x ∧
                      ¬ SourceOnlyPredicateCapturesSideEq u
                        (fun x => v x c) (v x c)))) ∧
  (∀ {Z Coin V : Type} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool),
      (∀ u, y (tiInputMap u) = !(y u)) →
        (∀ u, w (tiInputMap u) = w u) →
          (∀ u c, 0 < w u * coinWeight c → v (tiInputMap u) c = v u c) →
            ¬ 0 < doubledAdvantage
                (fun xr : PostSwitchInput Z k × Coin =>
                  (invariantProjection xr.1, v xr.1 xr.2))
                (fun xr : PostSwitchInput Z k × Coin => y xr.1)
                (productWeight w coinWeight) h) ∧
  (∀ {Z Coin V : Type} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool),
      (∀ u, y (tiInputMap u) = !(y u)) →
        (∀ u, w (tiInputMap u) = w u) →
          exactInputInvariantWeightedSupport w →
            ¬ weightedTotalMass (productWeight w coinWeight) <
              2 * weightedCorrectMass
                (fun xr : PostSwitchInput Z k × Coin =>
                  (invariantProjection xr.1, v xr.1 xr.2))
                (fun xr : PostSwitchInput Z k × Coin => y xr.1)
                (productWeight w coinWeight) h) ∧
  ∀ {Z Coin V : Type} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool),
      (∀ u, y (tiInputMap u) = !(y u)) →
        (∀ u, w (tiInputMap u) = w u) →
          weightedTotalMass (productWeight w coinWeight) <
            2 * weightedCorrectMass
              (fun xr : PostSwitchInput Z k × Coin =>
                (invariantProjection xr.1, v xr.1 xr.2))
              (fun xr : PostSwitchInput Z k × Coin => y xr.1)
              (productWeight w coinWeight) h →
            ∃ c, 0 < coinWeight c ∧
              (¬ SideInfoDeterminedBy invariantProjection (fun u => v u c) ∧
                PositiveWeightSideInfoCollisionOverBase invariantProjection
                  (fun u => v u c) w ∧
                (∃ u, 0 < w u ∧
                  invariantProjection (tiInputMap u) = invariantProjection u ∧
                  v (tiInputMap u) c ≠ v u c) ∧
                (∃ u, 0 < w u ∧
                  ¬ SourceOnlyPredicateCapturesSideEq invariantProjection
                    (fun u => v u c) (v u c)))

theorem randomizedResidualCoverage :
    RandomizedResidualCoverage := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro α Coin U V _Fintypeα _FintypeCoin τ u v y w coinWeight h hτ hu hy hw hadv
    exact
      randomizedResidualCoverage_anchor_positive_advantage_witnesses_deterministic_coin_slice
        τ u v y w coinWeight h hτ hu hy hw hadv
  · intro α Coin U V _Fintypeα _FintypeCoin τ u v y w coinWeight h hτ hu hy hw hadv
    exact
      randomizedResidualCoverage_anchor_strict_half_advantage_coin_slice_forces_residual_obstruction_package
        τ u v y w coinWeight h hτ hu hy hw hadv
  · intro Z Coin V k _FintypeZ _FintypeCoin v y w coinWeight h hy hw hunresolved
    exact
      randomizedResidualCoverage_anchor_postSwitch_supportwise_unresolved_no_positive_advantage
        v y w coinWeight h hy hw hunresolved
  · intro Z Coin V k _FintypeZ _FintypeCoin v y w coinWeight h hy hw hsupport
    exact
      randomizedResidualCoverage_anchor_postSwitch_exact_support_no_strict_half_advantage
        v y w coinWeight h hy hw hsupport
  · intro Z Coin V k _FintypeZ _FintypeCoin v y w coinWeight h hy hw hadv
    exact
      randomizedResidualCoverage_anchor_postSwitch_strict_half_advantage_coin_slice_forces_residual_obstruction_package
        v y w coinWeight h hy hw hadv

end Mettapedia.Computability.PNP
