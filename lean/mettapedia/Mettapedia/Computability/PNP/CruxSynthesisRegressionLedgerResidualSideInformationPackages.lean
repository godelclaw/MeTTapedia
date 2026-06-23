import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialPackagesCore
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialPackagesSupported
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialPackagesNoVisiblePairBalancing
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsExistentialPackagesExactSuccess

/-!
# Regression checks for residual-side-information support packages

Pure residual, supported-obstruction-package, and exact-success wrappers
extracted from the historical residual-side-information ledger regression
module.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem residual_side_information_existential_positive_advantage_repair_exposes_pure_residual_obstruction_package_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) := by
  exact
    residualSideInformationCoverage_anchor_existential_positive_advantage_repair_exposes_pure_residual_obstruction_package
      τ base side y w hτ hbase hy hw hsuccess

theorem residual_side_information_existential_positive_advantage_repair_exposes_supported_obstruction_package_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
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
    residualSideInformationCoverage_anchor_existential_positive_advantage_repair_exposes_supported_obstruction_package
      τ base side y w hτ hbase hy hw hsuccess

theorem residual_side_information_existential_strict_half_repair_exposes_supported_obstruction_package_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
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
    residualSideInformationCoverage_anchor_existential_strict_half_repair_exposes_supported_obstruction_package
      τ base side y w hτ hbase hy hw hsuccess

theorem residual_side_information_existential_strict_half_repair_exposes_pure_residual_obstruction_package_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      PositiveWeightSideInfoCollisionOverBase base side w ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) := by
  exact
    residualSideInformationCoverage_anchor_existential_strict_half_repair_exposes_pure_residual_obstruction_package
      τ base side y w hτ hbase hy hw hsuccess

theorem residual_side_information_existential_positive_advantage_repair_iff_supported_obstruction_package_regression
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
    residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_supported_obstruction_package
      τ base side y w hτ hbase hy hw

theorem residual_side_information_existential_positive_advantage_repair_iff_supported_obstruction_package_and_no_visible_pair_balancing_regression
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
    residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_supported_obstruction_package_and_no_visible_pair_balancing
      τ base side y w hτ hbase hy hw

theorem residual_side_information_existential_exact_supported_success_iff_full_resolution_budget_and_supported_obstruction_package_and_no_visible_pair_balancing_regression
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
    residualSideInformationCoverage_anchor_existential_exact_supported_success_iff_full_resolution_budget_and_supported_obstruction_package_and_no_visible_pair_balancing
      τ base side y w hτ hbase hy hw

theorem residual_side_information_existential_exact_supported_success_iff_full_resolution_budget_and_resolving_witness_regression
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
    residualSideInformationCoverage_anchor_existential_exact_supported_success_iff_full_resolution_budget_and_resolving_witness
      τ base side y w hτ hbase hy hw

theorem residual_side_information_existential_strict_half_repair_iff_supported_obstruction_package_regression
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
    residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_supported_obstruction_package
      τ base side y w hτ hbase hy hw

theorem residual_side_information_existential_strict_half_repair_iff_supported_obstruction_package_and_no_visible_pair_balancing_regression
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
    residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_supported_obstruction_package_and_no_visible_pair_balancing
      τ base side y w hτ hbase hy hw

end Mettapedia.Computability.PNP.CruxSynthesisRegression
