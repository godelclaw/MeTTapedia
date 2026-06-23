import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostAdvantageVisiblePair

/-!
# Residual side-information resolution cost: visible-pair balancing

Supportwise visible-pair balancing involutions and their direct advantage blockers.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- A supportwise visible-pair balancing involution flips the target, preserves
weights, and keeps the visible `(base, side)` pair fixed on positive support. -/
def SupportwiseVisiblePairBalancing
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) : Prop :=
  ∃ σ : α → α,
    Function.Involutive σ ∧
    (∀ x, y (σ x) = !(y x)) ∧
    (∀ x, w (σ x) = w x) ∧
    (∀ x, 0 < w x → (base (σ x), side (σ x)) = (base x, side x))

/-- A successful classifier on `(base, side)` rules out every supportwise
visible-pair balancing involution on that visible surface. -/
theorem not_supportwiseVisiblePairBalancing_of_pos_doubledAdvantage_pair
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ¬ SupportwiseVisiblePairBalancing base side y w := by
  rintro ⟨σ, hσ, hy, hw, hpair⟩
  exact
    (not_pos_doubledAdvantage_pair_of_supportwise_visiblePair_invariant
      σ base side y w h hσ hy hw hpair) hadv

/-- The same visible-pair balancing obstruction blocks any strict half-accuracy
success on `(base, side)`. -/
theorem not_supportwiseVisiblePairBalancing_of_total_lt_two_mul_weightedCorrectMass_pair
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ¬ SupportwiseVisiblePairBalancing base side y w := by
  rintro ⟨σ, hσ, hy, hw, hpair⟩
  exact
    (not_total_lt_two_mul_weightedCorrectMass_pair_of_supportwise_visiblePair_invariant
      σ base side y w h hσ hy hw hpair) hadv

end

end Mettapedia.Computability.PNP
