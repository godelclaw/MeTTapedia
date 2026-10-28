import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesPure
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesBalancing
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesWitnesses
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesAnySuccess

/-!
# Regression checks for PNP residual-side-information orbit-invisible blockers

This module keeps the historical `CruxSynthesisRegression` theorem namespace
while isolating the orbit-invisible and visible-pair-balancing blockers.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem residual_side_information_anchor_supported_non_source_determined_not_sufficient_for_positive_resolved_mass_or_success_regression
    :
    Function.Involutive OrbitInvisibleResidualCounterexample.orbitSwap ∧
      (∀ x, OrbitInvisibleResidualCounterexample.base
          (OrbitInvisibleResidualCounterexample.orbitSwap x) =
            OrbitInvisibleResidualCounterexample.base x) ∧
      (∀ x, OrbitInvisibleResidualCounterexample.side
          (OrbitInvisibleResidualCounterexample.orbitSwap x) =
            OrbitInvisibleResidualCounterexample.side x) ∧
      (∀ x, OrbitInvisibleResidualCounterexample.target
          (OrbitInvisibleResidualCounterexample.orbitSwap x) =
            !(OrbitInvisibleResidualCounterexample.target x)) ∧
      (∀ x, OrbitInvisibleResidualCounterexample.weight
          (OrbitInvisibleResidualCounterexample.orbitSwap x) =
            OrbitInvisibleResidualCounterexample.weight x) ∧
      ¬ SideInfoDeterminedBy
        OrbitInvisibleResidualCounterexample.base
        OrbitInvisibleResidualCounterexample.side ∧
      PositiveWeightSideInfoCollisionOverBase
        OrbitInvisibleResidualCounterexample.base
        OrbitInvisibleResidualCounterexample.side
        OrbitInvisibleResidualCounterexample.weight ∧
      (∃ x, 0 < OrbitInvisibleResidualCounterexample.weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq
          OrbitInvisibleResidualCounterexample.base
          OrbitInvisibleResidualCounterexample.side
          (OrbitInvisibleResidualCounterexample.side x)) ∧
      resolvedMass
        OrbitInvisibleResidualCounterexample.orbitSwap
        OrbitInvisibleResidualCounterexample.side
        OrbitInvisibleResidualCounterexample.weight = 0 ∧
      (∃ h : Unit × Bool → Bool,
        ¬ SupportwiseSourceOnlyPairClassifier
          OrbitInvisibleResidualCounterexample.base
          OrbitInvisibleResidualCounterexample.side
          OrbitInvisibleResidualCounterexample.weight h ∧
        ¬ 0 < doubledAdvantage
          (fun x =>
            (OrbitInvisibleResidualCounterexample.base x,
              OrbitInvisibleResidualCounterexample.side x))
          OrbitInvisibleResidualCounterexample.target
          OrbitInvisibleResidualCounterexample.weight h ∧
        ¬ weightedTotalMass OrbitInvisibleResidualCounterexample.weight <
          2 * weightedCorrectMass
            (fun x =>
              (OrbitInvisibleResidualCounterexample.base x,
                OrbitInvisibleResidualCounterexample.side x))
            OrbitInvisibleResidualCounterexample.target
            OrbitInvisibleResidualCounterexample.weight h) ∧
      (∀ h : Unit × Bool → Bool,
        ¬ 0 < doubledAdvantage
          (fun x =>
            (OrbitInvisibleResidualCounterexample.base x,
              OrbitInvisibleResidualCounterexample.side x))
          OrbitInvisibleResidualCounterexample.target
          OrbitInvisibleResidualCounterexample.weight h) ∧
      (∀ h : Unit × Bool → Bool,
        ¬ weightedTotalMass OrbitInvisibleResidualCounterexample.weight <
          2 * weightedCorrectMass
            (fun x =>
              (OrbitInvisibleResidualCounterexample.base x,
                OrbitInvisibleResidualCounterexample.side x))
            OrbitInvisibleResidualCounterexample.target
            OrbitInvisibleResidualCounterexample.weight h) := by
  exact
    residualSideInformationCoverage_anchor_supported_non_source_determined_not_sufficient_for_positive_resolvedMass_or_success

theorem residual_side_information_anchor_supportwise_visible_pair_balancing_blocks_any_classifier_success_regression
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
  exact
    residualSideInformationCoverage_anchor_supportwise_visible_pair_balancing_blocks_any_classifier_success
      σ base side y w hσ hy hw hpair

end Mettapedia.Computability.PNP.CruxSynthesisRegression
