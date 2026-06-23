import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialPackagesSupported

/-!
# PNP residual-side-information anchors: visible-pair balancing sharpenings

This module adds the no-visible-pair-balancing burden to the existential
supported-obstruction-package equivalences.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: over an invariant base, existential positive
advantage residual repair is exactly equivalent to the full supported
obstruction package plus the generic no-visible-pair-balancing burden. -/
theorem residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_supported_obstruction_package_and_no_visible_pair_balancing
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  exact
    exists_pos_doubledAdvantage_iff_exists_supported_obstruction_package_and_no_visiblePairBalancing_invariant_base
      τ base side y w hτ hbase hy hw

/-- Route-coverage anchor: the same final sharpening holds for existential
strict half-accuracy residual repair. -/
theorem residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_supported_obstruction_package_and_no_visible_pair_balancing
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
      ¬ SupportwiseVisiblePairBalancing base side y w := by
  exact
    exists_total_lt_two_mul_weightedCorrectMass_iff_exists_supported_obstruction_package_and_no_visiblePairBalancing_invariant_base
      τ base side y w hτ hbase hy hw

end Mettapedia.Computability.PNP
