import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesCore
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesPositive
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesStrictHalf
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesPrediction
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesSupportedPackages

/-!
# PNP residual-side-information V13 advantage-consequence subcoverage

This module packages the V13 positive/strict-half advantage consequences.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- The V13 advantage-consequence layer: any surviving positive or strict-half
advantage forces non-source-determination, positive-weight collisions,
supported non-source-only predicates, and prediction separation. -/
def V13ResidualSideInformationAdvantageConsequenceSubcoverage : Prop :=
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage (fun x => (base x, side x)) y w h →
                ¬ ∀ x, 0 < w x → (base (τ x), side (τ x)) = (base x, side x)) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h →
                ¬ ∀ x, 0 < w x → (base (τ x), side (τ x)) = (base x, side x)) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage (fun x => (base x, side x)) y w h →
                ¬ SideInfoDeterminedBy base side) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h →
                ¬ SideInfoDeterminedBy base side) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage (fun x => (base x, side x)) y w h →
                PositiveWeightSideInfoCollisionOverBase base side w) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage (fun x => (base x, side x)) y w h →
                ∃ x, 0 < w x ∧
                  ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              (∀ x, 0 < w x →
                SourceOnlyPredicateCapturesSideEq base side (side x)) →
                  ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              SupportwiseSourceOnlyPairClassifier base side w h →
                ¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h →
                PositiveWeightSideInfoCollisionOverBase base side w) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h →
                ∃ x, 0 < w x ∧
                  ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              (∀ x, 0 < w x →
                SourceOnlyPredicateCapturesSideEq base side (side x)) →
                  ¬ weightedTotalMass w <
                    2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              SupportwiseSourceOnlyPairClassifier base side w h →
                ¬ weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              0 < doubledAdvantage (fun x => (base x, side x)) y w h →
                ∃ x, 0 < w x ∧
                  h (base (τ x), side (τ x)) ≠ h (base x, side x)) ∧
  (∀ {α : Type u} {Base : Type v} {Side : Type w} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool),
      Function.Involutive τ →
        (∀ x, base (τ x) = base x) →
          (∀ x, y (τ x) = !(y x)) →
            (∀ x, w (τ x) = w x) →
              weightedTotalMass w <
                  2 * weightedCorrectMass (fun x => (base x, side x)) y w h →
                ∃ x, 0 < w x ∧
                  h (base (τ x), side (τ x)) ≠ h (base x, side x))

@[simp] theorem v13ResidualSideInformationAdvantageConsequenceSubcoverage :
    V13ResidualSideInformationAdvantageConsequenceSubcoverage := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_positive_advantage_forces_visible_pair_asymmetry
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_strict_half_advantage_forces_visible_pair_asymmetry
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_positive_advantage_forces_not_source_determined
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_strict_half_advantage_forces_not_source_determined
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_positive_advantage_positiveWeight_collision
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_positive_advantage_blocks_supported_source_predicate
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hsource
    exact
      residualSideInformationCoverage_anchor_supported_source_predicates_no_positive_advantage
        τ base side y w h hτ hbase hy hw hsource
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hsource
    exact
      residualSideInformationCoverage_anchor_supportwise_source_classifier_no_positive_advantage
        τ base side y w h hτ hbase hy hw hsource
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_strict_half_advantage_positiveWeight_collision
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_strict_half_advantage_blocks_supported_source_predicate
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hsource
    exact
      residualSideInformationCoverage_anchor_supported_source_predicates_no_strict_half_advantage
        τ base side y w h hτ hbase hy hw hsource
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hsource
    exact
      residualSideInformationCoverage_anchor_supportwise_source_classifier_no_strict_half_advantage
        τ base side y w h hτ hbase hy hw hsource
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_positive_advantage_prediction_separation
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_strict_half_advantage_prediction_separation
        τ base side y w h hτ hbase hy hw hadv

end Mettapedia.Computability.PNP
