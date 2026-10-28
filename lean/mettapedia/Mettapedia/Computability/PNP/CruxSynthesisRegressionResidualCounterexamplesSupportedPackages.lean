import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesPure
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesBalancing
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesWitnesses
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesAnySuccess

/-!
# Regression checks for PNP residual-side-information supported package blockers

This module keeps the historical `CruxSynthesisRegression` theorem namespace
while isolating the supported obstruction packages that are still insufficient
for success.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem residual_side_information_anchor_supported_obstruction_package_not_sufficient_for_success_regression
    :
    ∃ h : Unit × Bool → Bool,
      0 < resolvedMass
        BalancedResidualCounterexample.resolveSwap
        BalancedResidualCounterexample.side
        BalancedResidualCounterexample.weight ∧
      ¬ SideInfoDeterminedBy
        BalancedResidualCounterexample.base
        BalancedResidualCounterexample.side ∧
      ¬ SupportwiseSourceOnlyPairClassifier
        BalancedResidualCounterexample.base
        BalancedResidualCounterexample.side
        BalancedResidualCounterexample.weight h ∧
      (∃ x, 0 < BalancedResidualCounterexample.weight x ∧
        BalancedResidualCounterexample.base
            (BalancedResidualCounterexample.resolveSwap x) =
          BalancedResidualCounterexample.base x ∧
        BalancedResidualCounterexample.side
            (BalancedResidualCounterexample.resolveSwap x) ≠
          BalancedResidualCounterexample.side x) ∧
      (∃ x, 0 < BalancedResidualCounterexample.weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq
          BalancedResidualCounterexample.base
          BalancedResidualCounterexample.side
          (BalancedResidualCounterexample.side x)) ∧
      (∃ x, 0 < BalancedResidualCounterexample.weight x ∧
        h
            (BalancedResidualCounterexample.base
              (BalancedResidualCounterexample.resolveSwap x),
              BalancedResidualCounterexample.side
                (BalancedResidualCounterexample.resolveSwap x)) ≠
          h
            (BalancedResidualCounterexample.base x,
              BalancedResidualCounterexample.side x)) ∧
      ¬ 0 < doubledAdvantage
        (fun x =>
          (BalancedResidualCounterexample.base x,
            BalancedResidualCounterexample.side x))
        BalancedResidualCounterexample.target
        BalancedResidualCounterexample.weight h ∧
      ¬ weightedTotalMass BalancedResidualCounterexample.weight <
        2 * weightedCorrectMass
          (fun x =>
          (BalancedResidualCounterexample.base x,
              BalancedResidualCounterexample.side x))
          BalancedResidualCounterexample.target
          BalancedResidualCounterexample.weight h := by
  exact
    residualSideInformationCoverage_anchor_supported_obstruction_package_not_sufficient_for_success

theorem residual_side_information_anchor_supported_obstruction_package_not_sufficient_for_any_success_regression
    :
    ∃ h : Unit × Bool → Bool,
      0 < resolvedMass
        BalancedResidualCounterexample.resolveSwap
        BalancedResidualCounterexample.side
        BalancedResidualCounterexample.weight ∧
      ¬ SideInfoDeterminedBy
        BalancedResidualCounterexample.base
        BalancedResidualCounterexample.side ∧
      ¬ SupportwiseSourceOnlyPairClassifier
        BalancedResidualCounterexample.base
        BalancedResidualCounterexample.side
        BalancedResidualCounterexample.weight h ∧
      (∃ x, 0 < BalancedResidualCounterexample.weight x ∧
        BalancedResidualCounterexample.base
            (BalancedResidualCounterexample.resolveSwap x) =
          BalancedResidualCounterexample.base x ∧
        BalancedResidualCounterexample.side
            (BalancedResidualCounterexample.resolveSwap x) ≠
          BalancedResidualCounterexample.side x) ∧
      (∃ x, 0 < BalancedResidualCounterexample.weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq
          BalancedResidualCounterexample.base
          BalancedResidualCounterexample.side
          (BalancedResidualCounterexample.side x)) ∧
      (∃ x, 0 < BalancedResidualCounterexample.weight x ∧
        h
            (BalancedResidualCounterexample.base
              (BalancedResidualCounterexample.resolveSwap x),
              BalancedResidualCounterexample.side
                (BalancedResidualCounterexample.resolveSwap x)) ≠
          h
            (BalancedResidualCounterexample.base x,
              BalancedResidualCounterexample.side x)) ∧
      (∀ h' : Unit × Bool → Bool,
        ¬ 0 < doubledAdvantage
          (fun x =>
            (BalancedResidualCounterexample.base x,
              BalancedResidualCounterexample.side x))
          BalancedResidualCounterexample.target
          BalancedResidualCounterexample.weight h') ∧
      (∀ h' : Unit × Bool → Bool,
        ¬ weightedTotalMass BalancedResidualCounterexample.weight <
          2 * weightedCorrectMass
            (fun x =>
              (BalancedResidualCounterexample.base x,
                BalancedResidualCounterexample.side x))
            BalancedResidualCounterexample.target
            BalancedResidualCounterexample.weight h') := by
  exact
    residualSideInformationCoverage_anchor_supported_obstruction_package_not_sufficient_for_any_success

theorem residual_side_information_anchor_supported_obstruction_package_with_visible_pair_balancing_blocks_any_success_regression
    :
    ∃ h : Unit × Bool → Bool,
      0 < resolvedMass
        BalancedResidualCounterexample.resolveSwap
        BalancedResidualCounterexample.side
        BalancedResidualCounterexample.weight ∧
      ¬ SideInfoDeterminedBy
        BalancedResidualCounterexample.base
        BalancedResidualCounterexample.side ∧
      ¬ SupportwiseSourceOnlyPairClassifier
        BalancedResidualCounterexample.base
        BalancedResidualCounterexample.side
        BalancedResidualCounterexample.weight h ∧
      (∃ x, 0 < BalancedResidualCounterexample.weight x ∧
        BalancedResidualCounterexample.base
            (BalancedResidualCounterexample.resolveSwap x) =
          BalancedResidualCounterexample.base x ∧
        BalancedResidualCounterexample.side
            (BalancedResidualCounterexample.resolveSwap x) ≠
          BalancedResidualCounterexample.side x) ∧
      (∃ x, 0 < BalancedResidualCounterexample.weight x ∧
        ¬ SourceOnlyPredicateCapturesSideEq
          BalancedResidualCounterexample.base
          BalancedResidualCounterexample.side
          (BalancedResidualCounterexample.side x)) ∧
      (∃ x, 0 < BalancedResidualCounterexample.weight x ∧
        h
            (BalancedResidualCounterexample.base
              (BalancedResidualCounterexample.resolveSwap x),
              BalancedResidualCounterexample.side
                (BalancedResidualCounterexample.resolveSwap x)) ≠
          h
            (BalancedResidualCounterexample.base x,
              BalancedResidualCounterexample.side x)) ∧
      Function.Involutive BalancedResidualCounterexample.neutralSwap ∧
      (∀ x, BalancedResidualCounterexample.target
          (BalancedResidualCounterexample.neutralSwap x) =
            !(BalancedResidualCounterexample.target x)) ∧
      (∀ x, BalancedResidualCounterexample.weight
          (BalancedResidualCounterexample.neutralSwap x) =
            BalancedResidualCounterexample.weight x) ∧
      (∀ x, 0 < BalancedResidualCounterexample.weight x →
        (BalancedResidualCounterexample.base
            (BalancedResidualCounterexample.neutralSwap x),
          BalancedResidualCounterexample.side
            (BalancedResidualCounterexample.neutralSwap x)) =
          (BalancedResidualCounterexample.base x,
            BalancedResidualCounterexample.side x)) ∧
      (∀ h' : Unit × Bool → Bool,
        ¬ 0 < doubledAdvantage
          (fun x =>
            (BalancedResidualCounterexample.base x,
              BalancedResidualCounterexample.side x))
          BalancedResidualCounterexample.target
          BalancedResidualCounterexample.weight h') ∧
      (∀ h' : Unit × Bool → Bool,
        ¬ weightedTotalMass BalancedResidualCounterexample.weight <
          2 * weightedCorrectMass
            (fun x =>
              (BalancedResidualCounterexample.base x,
                BalancedResidualCounterexample.side x))
            BalancedResidualCounterexample.target
            BalancedResidualCounterexample.weight h') := by
  exact
    residualSideInformationCoverage_anchor_supported_obstruction_package_with_visible_pair_balancing_blocks_any_success

end Mettapedia.Computability.PNP.CruxSynthesisRegression
