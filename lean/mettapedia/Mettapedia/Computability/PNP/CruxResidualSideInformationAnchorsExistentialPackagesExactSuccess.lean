import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialPackagesNoVisiblePairBalancing

/-!
# PNP residual-side-information anchors: exact supported success

This module characterizes exact supported success by the full residual-resolution
budget, supported obstruction data, and the minimal resolving-witness boundary.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: positive-support exact supported success over an
invariant base is exactly equivalent to a witness classifier whose doubled
advantage saturates the full orbit-resolving budget, together with the full
supported obstruction package and the generic no-visible-pair-balancing
burden. -/
theorem residualSideInformationCoverage_anchor_existential_exact_supported_success_iff_full_resolution_budget_and_supported_obstruction_package_and_no_visible_pair_balancing
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ((∃ h : Base × Side → Bool,
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w) ∧
      0 < weightedTotalMass w) ↔
    ∃ h : Base × Side → Bool,
      doubledAdvantage (fun x => (base x, side x)) y w h =
          resolvedMass τ side w ∧
        resolvedMass τ side w = weightedTotalMass w ∧
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
    exists_weightedCorrectMass_eq_weightedTotalMass_and_pos_totalMass_iff_exists_full_resolution_budget_and_supported_obstruction_package_and_no_visiblePairBalancing_invariant_base
      τ base side y w hτ hbase hy hw

/-- Route-coverage anchor: the exact supported-success claim also collapses to
the minimal proof-relevant burden that matters for the residual-side route: a
witness classifier saturating the full resolution budget and exposing a
supported same-base residual witness. -/
theorem residualSideInformationCoverage_anchor_existential_exact_supported_success_iff_full_resolution_budget_and_resolving_witness
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ((∃ h : Base × Side → Bool,
      weightedCorrectMass (fun x => (base x, side x)) y w h =
        weightedTotalMass w) ∧
      0 < weightedTotalMass w) ↔
    ∃ h : Base × Side → Bool,
      doubledAdvantage (fun x => (base x, side x)) y w h =
          resolvedMass τ side w ∧
        resolvedMass τ side w = weightedTotalMass w ∧
        0 < resolvedMass τ side w ∧
        (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) := by
  exact
    exists_weightedCorrectMass_eq_weightedTotalMass_and_pos_totalMass_iff_exists_full_resolution_budget_and_same_base_residual_witness_invariant_base
      τ base side y w hτ hbase hy hw

end Mettapedia.Computability.PNP
