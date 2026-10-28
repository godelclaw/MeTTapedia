import Mettapedia.Computability.PNP.CruxRandomizedResidualAnchorsFiniteCoin
import Mettapedia.Computability.PNP.CruxRandomizedResidualAnchorsPostSwitchFiniteCoin

/-!
# PNP randomized-residual V13 subcoverage specification

Named V13 randomized-residual subcoverages.  The proof file assembles these
from the finite-coin and exact-post-switch theorem-backed anchors.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Finite-coin residual budget bounds and supportwise-unresolved blockers. -/
def V13RandomizedResidualFiniteCoinBudgetCoverage : Prop :=
  (∀ {α : Type u} {Coin : Type v} {U : Type w} {V : Type z} [Fintype α] [Fintype Coin]
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
  (∀ {α : Type u} {Coin : Type v} {V : Type z} [Fintype α] [Fintype Coin]
    (τ : α → α) (v : α → Coin → V)
    (w : α → ℕ) (coinWeight : Coin → ℕ),
      (∀ x c, 0 < w x * coinWeight c → v (τ x) c = v x c) →
        randomizedResidualResolvedMass τ v w coinWeight = 0) ∧
  (∀ {α : Type u} {Coin : Type v} {U : Type w} {V : Type z} [Fintype α] [Fintype Coin]
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
                    (productWeight w coinWeight) h)

/-- Finite-coin positive-advantage and strict-half surfaces expose resolving
coins and deterministic residual-side-information slices. -/
def V13RandomizedResidualFiniteCoinWitnessCoverage : Prop :=
  (∀ {α : Type u} {Coin : Type v} {U : Type w} {V : Type z} [Fintype α] [Fintype Coin]
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
                ∃ x c, 0 < w x * coinWeight c ∧ v (τ x) c ≠ v x c) ∧
  (∀ {α : Type u} {Coin : Type v} {U : Type w} {V : Type z} [Fintype α] [Fintype Coin]
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
                ∃ c, 0 < coinWeight c ∧ 0 < resolvedMass τ (fun x => v x c) w) ∧
  (∀ {α : Type u} {Coin : Type v} {U : Type w} {V : Type z} [Fintype α] [Fintype Coin]
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
                  0 < resolvedMass τ (fun x => v x c) w) ∧
  (∀ {α : Type u} {Coin : Type v} {U : Type w} {V : Type z} [Fintype α] [Fintype Coin]
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
                        (fun x => v x c) (v x c))))

/-- Exact post-switch randomized-residual blockers. -/
def V13RandomizedResidualPostSwitchBlockerCoverage : Prop :=
  (∀ {Z : Type u} {Coin : Type v} {V : Type w} {k : ℕ} [Fintype Z] [Fintype Coin]
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
  (∀ {Z : Type u} {Coin : Type v} {V : Type w} {k : ℕ} [Fintype Z] [Fintype Coin]
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
                (productWeight w coinWeight) h)

/-- Exact post-switch randomized-residual witness and residual-package
consequences. -/
def V13RandomizedResidualPostSwitchWitnessCoverage : Prop :=
  (∀ {Z : Type u} {Coin : Type v} {V : Type w} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool),
      (∀ u, y (tiInputMap u) = !(y u)) →
        (∀ u, w (tiInputMap u) = w u) →
          0 < doubledAdvantage
              (fun xr : PostSwitchInput Z k × Coin =>
                (invariantProjection xr.1, v xr.1 xr.2))
              (fun xr : PostSwitchInput Z k × Coin => y xr.1)
              (productWeight w coinWeight) h →
            ∃ u c, 0 < w u * coinWeight c ∧ v (tiInputMap u) c ≠ v u c) ∧
  (∀ {Z : Type u} {Coin : Type v} {V : Type w} {k : ℕ} [Fintype Z] [Fintype Coin]
    (v : PostSwitchInput Z k → Coin → V)
    (y : PostSwitchInput Z k → Bool)
    (w : PostSwitchInput Z k → ℕ) (coinWeight : Coin → ℕ)
    (h : (Z × BitVec k) × V → Bool),
      (∀ u, y (tiInputMap u) = !(y u)) →
        (∀ u, w (tiInputMap u) = w u) →
          0 < doubledAdvantage
              (fun xr : PostSwitchInput Z k × Coin =>
                (invariantProjection xr.1, v xr.1 xr.2))
              (fun xr : PostSwitchInput Z k × Coin => y xr.1)
              (productWeight w coinWeight) h →
            ∃ c, 0 < coinWeight c ∧
              0 < resolvedMass tiInputMap (fun u => v u c) w) ∧
  (∀ {Z : Type u} {Coin : Type v} {V : Type w} {k : ℕ} [Fintype Z] [Fintype Coin]
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
              0 < resolvedMass tiInputMap (fun u => v u c) w) ∧
  ∀ {Z : Type u} {Coin : Type v} {V : Type w} {k : ℕ} [Fintype Z] [Fintype Coin]
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

/-- The current randomized-residual subledger is theorem-backed at the narrow
finite-coin/product boundary and exact post-switch specialization. -/
def V13RandomizedResidualSubcoverage : Prop :=
  V13RandomizedResidualFiniteCoinBudgetCoverage.{u, v, w, z} ∧
    V13RandomizedResidualFiniteCoinWitnessCoverage.{u, v, w, z} ∧
      V13RandomizedResidualPostSwitchBlockerCoverage.{u, v, w} ∧
        V13RandomizedResidualPostSwitchWitnessCoverage.{u, v, w}

end Mettapedia.Computability.PNP
