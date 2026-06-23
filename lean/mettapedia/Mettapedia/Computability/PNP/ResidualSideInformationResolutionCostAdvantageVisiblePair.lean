import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostAdvantageStrictHalf

/-!
# Residual side-information resolution cost: visible-pair symmetry blockers

Supportwise visible-pair invariance blocks positive doubled advantage and strict half-accuracy advantage.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- If a weight-preserving involution flips the target while keeping the
visible `(base, side)` feature pair fixed on positive support, then no
classifier on `(base, side)` can have positive doubled advantage. -/
theorem not_pos_doubledAdvantage_pair_of_supportwise_visiblePair_invariant
    (σ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hσ : Function.Involutive σ)
    (hy : ∀ x, y (σ x) = !(y x))
    (hw : ∀ x, w (σ x) = w x)
    (hpair : ∀ x, 0 < w x → (base (σ x), side (σ x)) = (base x, side x)) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
  have hpred :
      ∀ x, 0 < w x →
        h (base (σ x), side (σ x)) = h (base x, side x) := by
    intro x hx
    exact congrArg h (hpair x hx)
  exact
    not_pos_doubledAdvantage_of_supportwise_prediction_invariant
      σ (fun x => (base x, side x)) y w h hσ hy hw hpred

/-- The same supportwise visible-pair balancing symmetry also blocks strict
half-accuracy advantage on `(base, side)`. -/
theorem not_total_lt_two_mul_weightedCorrectMass_pair_of_supportwise_visiblePair_invariant
    (σ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hσ : Function.Involutive σ)
    (hy : ∀ x, y (σ x) = !(y x))
    (hw : ∀ x, w (σ x) = w x)
    (hpair : ∀ x, 0 < w x → (base (σ x), side (σ x)) = (base x, side x)) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  have hpred :
      ∀ x, 0 < w x →
        h (base (σ x), side (σ x)) = h (base x, side x) := by
    intro x hx
    exact congrArg h (hpair x hx)
  exact
    not_total_lt_two_mul_weightedCorrectMass_of_supportwise_prediction_invariant
      σ (fun x => (base x, side x)) y w h hσ hy hw hpred

end

end Mettapedia.Computability.PNP
