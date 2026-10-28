import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialWitnessesCore

/-!
# PNP residual-side-information anchors: existential witnesses with visible-balancing blockers

Resolving-witness boundaries sharpened by the absence of supportwise visible-pair balancing.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: over an invariant base, existential positive
residual repair is exactly the same claim plus the minimal resolving witness
and absence of any supportwise visible-pair-balancing involution on the same
visible surface. -/
theorem residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_resolving_witness_and_no_visible_pair_balancing
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ((∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w) := by
  exact
    exists_pos_doubledAdvantage_iff_exists_classifier_and_same_base_residual_witness_and_no_visiblePairBalancing_invariant_base
      τ base side y w hτ hbase hy hw

/-- Route-coverage anchor: the same sharpening holds for existential strict
half-accuracy residual repair. -/
theorem residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_resolving_witness_and_no_visible_pair_balancing
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ((∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w) := by
  exact
    exists_total_lt_two_mul_weightedCorrectMass_iff_exists_classifier_and_same_base_residual_witness_and_no_visiblePairBalancing_invariant_base
      τ base side y w hτ hbase hy hw

end Mettapedia.Computability.PNP
