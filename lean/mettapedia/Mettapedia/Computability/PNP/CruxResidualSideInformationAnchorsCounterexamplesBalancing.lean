import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesPure

/-!
# PNP residual-side-information anchors: visible-pair balancing blockers

These route anchors isolate the generic balancing symmetry that blocks every
classifier over the visible `(base, side)` surface.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: any supportwise weight-preserving target-flipping
involution that leaves the visible `(base, side)` pair fixed blocks every
candidate residual repair on that visible surface.  So a successful residual
repair must rule out such balancing symmetries, not merely exhibit positive
resolved mass or a pure residual obstruction package. -/
theorem residualSideInformationCoverage_anchor_supportwise_visible_pair_balancing_blocks_any_classifier_success
    {α Base Side : Type*} [Fintype α]
    (σ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hσ : Function.Involutive σ)
    (hy : ∀ x, y (σ x) = !(y x))
    (hw : ∀ x, w (σ x) = w x)
    (hpair : ∀ x, 0 < w x → (base (σ x), side (σ x)) = (base x, side x)) :
    (¬ ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ∧
    (¬ ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) := by
  constructor
  · intro hexists
    rcases hexists with ⟨h, hadv⟩
    exact
      (not_pos_doubledAdvantage_pair_of_supportwise_visiblePair_invariant
        σ base side y w h hσ hy hw hpair) hadv
  · intro hexists
    rcases hexists with ⟨h, hadv⟩
    exact
      (not_total_lt_two_mul_weightedCorrectMass_pair_of_supportwise_visiblePair_invariant
        σ base side y w h hσ hy hw hpair) hadv

/-- Route-coverage anchor: any successful classifier on `(base, side)` already
rules out every supportwise visible-pair-balancing involution on that visible
surface. -/
theorem residualSideInformationCoverage_anchor_positive_advantage_forbids_visible_pair_balancing
    {α Base Side : Type*} [Fintype α]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ¬ SupportwiseVisiblePairBalancing base side y w :=
  not_supportwiseVisiblePairBalancing_of_pos_doubledAdvantage_pair
    base side y w h hadv

/-- Route-coverage anchor: the same balancing obstruction is impossible under
any strict half-accuracy success on `(base, side)`. -/
theorem residualSideInformationCoverage_anchor_strict_half_advantage_forbids_visible_pair_balancing
    {α Base Side : Type*} [Fintype α]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ¬ SupportwiseVisiblePairBalancing base side y w :=
  not_supportwiseVisiblePairBalancing_of_total_lt_two_mul_weightedCorrectMass_pair
    base side y w h hadv

end Mettapedia.Computability.PNP
