import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialWitnessesNoVisiblePairBalancing

/-!
# PNP residual-side-information anchors: visible-pair fiber imbalance

Finite visible-surface imbalance criteria for existential residual repair claims.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: on any finite visible `(base, side)` surface,
existential positive residual repair is exactly equivalent to a concrete
visible-pair fiber carrying unequal retained `true` and `false` mass. -/
theorem residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_visible_pair_fiber_imbalance
    {α Base Side : Type*} [Fintype α] [Fintype Base] [Fintype Side]
    [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) :
    (∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
      ∃ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  exact
    exists_pos_doubledAdvantage_pair_iff_exists_visiblePair_fiber_imbalance
      base side y w

/-- Route-coverage anchor: the same finite visible-surface exact criterion
holds for strict half-accuracy residual repair. -/
theorem residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_visible_pair_fiber_imbalance
    {α Base Side : Type*} [Fintype α] [Fintype Base] [Fintype Side]
    [DecidableEq Base] [DecidableEq Side]
    (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) :
    (∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
      ∃ bs : Base × Side,
        weightedFeatureFiberTrueMass (fun x => (base x, side x)) y w bs ≠
          weightedFeatureFiberFalseMass (fun x => (base x, side x)) y w bs := by
  exact
    exists_total_lt_two_mul_weightedCorrectMass_pair_iff_exists_visiblePair_fiber_imbalance
      base side y w

end Mettapedia.Computability.PNP
