import Mettapedia.Computability.PNP.RandomizedResidualObstruction

/-!
# PNP randomized-residual anchors: finite-coin residuals

Finite-coin randomized-residual anchors reducing randomized advantage to deterministic positive-weight coin slices.
-/

namespace Mettapedia.Computability.PNP

universe u v w z

/-- Route-coverage anchor: a supportwise-unresolved finite-coin randomized
residual cannot provide positive doubled advantage. -/
theorem randomizedResidualCoverage_anchor_supportwise_unresolved_no_positive_advantage
    {α Coin U V : Type*} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hunresolved :
      ∀ x c, 0 < w x * coinWeight c → v (τ x) c = v x c) :
    ¬ 0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h :=
  not_pos_doubledAdvantage_randomizedResidual_of_supportwise_unresolved
    τ u v y w coinWeight h hτ hu hy hw hunresolved

/-- Route-coverage anchor: positive finite-coin randomized-residual advantage
must expose a positive joint-support source/coin pair where the residual
changes across the involution. -/
theorem randomizedResidualCoverage_anchor_positive_advantage_witnesses_resolving_coin
    {α Coin U V : Type*} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ x c, 0 < w x * coinWeight c ∧ v (τ x) c ≠ v x c :=
  exists_resolving_coin_of_pos_doubledAdvantage_randomizedResidual
    τ u v y w coinWeight h hτ hu hy hw hadv

/-- Route-coverage anchor: positive finite-coin randomized-residual advantage
is already witnessed by a deterministic positive-weight coin slice with
positive ordinary side-channel resolving mass. -/
theorem randomizedResidualCoverage_anchor_positive_advantage_witnesses_deterministic_coin_slice
    {α Coin U V : Type*} [Fintype α] [Fintype Coin]
    (τ : α → α) (u : α → U) (v : α → Coin → V)
    (y : α → Bool) (w : α → ℕ) (coinWeight : Coin → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      0 < doubledAdvantage
        (fun xr : α × Coin => (u xr.1, v xr.1 xr.2))
        (fun xr : α × Coin => y xr.1)
        (productWeight w coinWeight) h) :
    ∃ c, 0 < coinWeight c ∧ 0 < resolvedMass τ (fun x => v x c) w :=
  exists_positive_coin_resolvedMass_of_pos_doubledAdvantage_randomizedResidual
    τ u v y w coinWeight h hτ hu hy hw hadv

/-- Route-coverage anchor: strict half-accuracy finite-coin randomized-
residual advantage is already witnessed by a deterministic positive-weight
coin slice with positive ordinary side-channel resolving mass. -/
theorem randomizedResidualCoverage_anchor_strict_half_advantage_witnesses_deterministic_coin_slice
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
    ∃ c, 0 < coinWeight c ∧ 0 < resolvedMass τ (fun x => v x c) w :=
  exists_positive_coin_resolvedMass_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual
    τ u v y w coinWeight h hτ hu hy hw hadv

/-- Route-coverage anchor: strict half-accuracy finite-coin randomized-
residual advantage is not an independent escape route.  It already yields a
deterministic positive-weight coin slice carrying the ordinary invariant-base
residual-side-information obstruction package. -/
theorem randomizedResidualCoverage_anchor_strict_half_advantage_coin_slice_forces_residual_obstruction_package
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
          ¬ SourceOnlyPredicateCapturesSideEq u (fun x => v x c) (v x c))) :=
  exists_positive_coin_obstruction_package_of_total_lt_two_mul_weightedCorrectMass_randomizedResidual
    τ u v y w coinWeight h hτ hu hy hw hadv

end Mettapedia.Computability.PNP
