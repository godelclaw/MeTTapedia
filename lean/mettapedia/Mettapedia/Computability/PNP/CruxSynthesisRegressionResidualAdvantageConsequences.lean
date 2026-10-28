import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesCore
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesPositive
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesStrictHalf
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesPrediction
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesSupportedPackages

/-!
# Regression checks for PNP residual-side-information anchors: positive-advantage and strict-half-advantage residual consequences

This module is part of the decomposed residual-side-information regression
ledger.  It keeps the historical `CruxSynthesisRegression` theorem namespace
while separating residual-anchor checks by mathematical role.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem residual_side_information_anchor_positive_advantage_forces_not_source_determined_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ¬ SideInfoDeterminedBy base side := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_forces_not_source_determined
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_positive_advantage_forces_visible_pair_asymmetry_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ¬ ∀ x, 0 < w x → (base (τ x), side (τ x)) = (base x, side x) := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_forces_visible_pair_asymmetry
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_strict_half_advantage_forces_not_source_determined_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ¬ SideInfoDeterminedBy base side := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_forces_not_source_determined
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_strict_half_advantage_forces_visible_pair_asymmetry_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ¬ ∀ x, 0 < w x → (base (τ x), side (τ x)) = (base x, side x) := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_forces_visible_pair_asymmetry
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_positive_advantage_witnesses_same_base_collision_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_witnesses_same_base_residual_collision
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_positive_advantage_positiveWeight_collision_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    PositiveWeightSideInfoCollisionOverBase base side w := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_positiveWeight_collision
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_positive_advantage_blocks_supported_source_predicate_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      ¬ SourceOnlyPredicateCapturesSideEq base side (side x) := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_blocks_supported_source_predicate
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_supported_source_predicates_no_positive_advantage_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource :
      ∀ x, 0 < w x → SourceOnlyPredicateCapturesSideEq base side (side x)) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
  exact
    residualSideInformationCoverage_anchor_supported_source_predicates_no_positive_advantage
      τ base side y w h hτ hbase hy hw hsource

theorem residual_side_information_anchor_supportwise_source_classifier_no_positive_advantage_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource : SupportwiseSourceOnlyPairClassifier base side w h) :
    ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h := by
  exact
    residualSideInformationCoverage_anchor_supportwise_source_classifier_no_positive_advantage
      τ base side y w h hτ hbase hy hw hsource

theorem residual_side_information_anchor_strict_half_advantage_witnesses_same_base_collision_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_witnesses_same_base_residual_collision
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_strict_half_advantage_positiveWeight_collision_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    PositiveWeightSideInfoCollisionOverBase base side w := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_positiveWeight_collision
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_strict_half_advantage_blocks_supported_source_predicate_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      ¬ SourceOnlyPredicateCapturesSideEq base side (side x) := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_blocks_supported_source_predicate
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_supported_source_predicates_no_strict_half_advantage_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource :
      ∀ x, 0 < w x → SourceOnlyPredicateCapturesSideEq base side (side x)) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  exact
    residualSideInformationCoverage_anchor_supported_source_predicates_no_strict_half_advantage
      τ base side y w h hτ hbase hy hw hsource

theorem residual_side_information_anchor_supportwise_source_classifier_no_strict_half_advantage_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsource : SupportwiseSourceOnlyPairClassifier base side w h) :
    ¬ weightedTotalMass w <
      2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  exact
    residualSideInformationCoverage_anchor_supportwise_source_classifier_no_strict_half_advantage
      τ base side y w h hτ hbase hy hw hsource

end Mettapedia.Computability.PNP.CruxSynthesisRegression
