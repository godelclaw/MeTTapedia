import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialPackagesCore

/-!
# PNP residual-side-information anchors: supported existential packages

This module records the exact supported-obstruction-package boundaries for
existential positive-advantage and strict-half residual repair.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: over an invariant base, an existential positive
advantage residual repair claim is exactly equivalent to existence of the full
supported obstruction package for some witness classifier. -/
theorem residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_supported_obstruction_package
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
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  exact
    exists_pos_doubledAdvantage_iff_exists_supported_obstruction_package_invariant_base
      τ base side y w hτ hbase hy hw

/-- Route-coverage anchor: the strict half-accuracy existential repair claim is
exactly equivalent to existence of the full supported obstruction package. -/
theorem residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_supported_obstruction_package
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
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  exact
    exists_total_lt_two_mul_weightedCorrectMass_iff_exists_supported_obstruction_package_invariant_base
      τ base side y w hτ hbase hy hw

end Mettapedia.Computability.PNP
