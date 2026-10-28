import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesCore
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesPositive
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesStrictHalf
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesPrediction
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsAdvantageConsequencesSupportedPackages

/-!
# Regression checks for PNP residual-side-information anchors: prediction-separation and supported-obstruction package checks

This module is part of the decomposed residual-side-information regression
ledger.  It keeps the historical `CruxSynthesisRegression` theorem namespace
while separating residual-anchor checks by mathematical role.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem residual_side_information_anchor_positive_advantage_prediction_separation_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ x, 0 < w x ∧
      h (base (τ x), side (τ x)) ≠ h (base x, side x) := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_prediction_separation
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_strict_half_advantage_prediction_separation_regression
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
      h (base (τ x), side (τ x)) ≠ h (base x, side x) := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_prediction_separation
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_positive_advantage_supported_obstruction_package_regression
    {α Base Side : Type*} [Fintype α]
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hadv : 0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  exact
    residualSideInformationCoverage_anchor_positive_advantage_forces_supported_obstruction_package
      τ base side y w h hτ hbase hy hw hadv

theorem residual_side_information_anchor_strict_half_advantage_supported_obstruction_package_regression
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
    0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x)) := by
  exact
    residualSideInformationCoverage_anchor_strict_half_advantage_forces_supported_obstruction_package
      τ base side y w h hτ hbase hy hw hadv

end Mettapedia.Computability.PNP.CruxSynthesisRegression
