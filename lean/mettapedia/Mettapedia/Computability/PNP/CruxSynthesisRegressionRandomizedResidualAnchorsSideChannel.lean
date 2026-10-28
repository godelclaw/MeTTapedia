import Mettapedia.Computability.PNP.CruxRandomizedResidualAnchorsSymmetry

/-!
# Regression checks for randomized-residual side-channel anchors

Regression wrappers for deterministic side-channel unresolvedness and positive-advantage witness anchors.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem side_channel_anchor_supportwise_unresolved_no_positive_advantage_regression
    {α U V : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (v : α → V)
    (y : α → Bool) (w : α → ℕ) (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hunresolved : ∀ x, 0 < w x → v (τ x) = v x) :
    ¬ 0 < doubledAdvantage (fun x => (u x, v x)) y w h := by
  exact
    sideChannelCoverage_anchor_supportwise_unresolved_no_positive_advantage
      τ u v y w h hτ hu hy hw hunresolved

theorem side_channel_anchor_positive_advantage_resolution_witness_regression
    {α U V : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (v : α → V)
    (y : α → Bool) (w : α → ℕ) (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (u x, v x)) y w h) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x := by
  exact
    sideChannelCoverage_anchor_positive_advantage_resolution_witness
      τ u v y w h hτ hu hy hw hadv

theorem side_channel_anchor_strict_half_accuracy_advantage_resolution_witness_regression
    {α U V : Type*} [Fintype α]
    (τ : α → α) (u : α → U) (v : α → V)
    (y : α → Bool) (w : α → ℕ) (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (u x, v x)) y w h) :
    ∃ x, 0 < w x ∧ v (τ x) ≠ v x := by
  exact
    sideChannelCoverage_anchor_strict_half_accuracy_advantage_resolution_witness
      τ u v y w h hτ hu hy hw hadv

end Mettapedia.Computability.PNP.CruxSynthesisRegression
