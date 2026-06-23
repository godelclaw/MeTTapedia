import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesPure
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesBalancing
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesWitnesses
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesAnySuccess

/-!
# Regression checks for PNP residual-side-information pure counterexamples

This module keeps the historical `CruxSynthesisRegression` theorem namespace
while isolating the pure residual obstruction counterexample.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem residual_side_information_anchor_pure_residual_obstruction_not_sufficient_for_success_regression :
    Function.Involutive BalancedResidualCounterexample.resolveSwap ∧
      (∀ x, BalancedResidualCounterexample.base
          (BalancedResidualCounterexample.resolveSwap x) =
            BalancedResidualCounterexample.base x) ∧
      (∀ x, BalancedResidualCounterexample.target
          (BalancedResidualCounterexample.resolveSwap x) =
            !(BalancedResidualCounterexample.target x)) ∧
      (∀ x, BalancedResidualCounterexample.weight
          (BalancedResidualCounterexample.resolveSwap x) =
            BalancedResidualCounterexample.weight x) ∧
      0 < resolvedMass
        BalancedResidualCounterexample.resolveSwap
        BalancedResidualCounterexample.side
        BalancedResidualCounterexample.weight ∧
      ¬ SideInfoDeterminedBy
        BalancedResidualCounterexample.base
        BalancedResidualCounterexample.side ∧
      PositiveWeightSideInfoCollisionOverBase
        BalancedResidualCounterexample.base
        BalancedResidualCounterexample.side
        BalancedResidualCounterexample.weight ∧
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
      (∀ h : Unit × Bool → Bool,
        ¬ 0 < doubledAdvantage
          (fun x =>
            (BalancedResidualCounterexample.base x,
              BalancedResidualCounterexample.side x))
          BalancedResidualCounterexample.target
          BalancedResidualCounterexample.weight h) ∧
      (∀ h : Unit × Bool → Bool,
        ¬ weightedTotalMass BalancedResidualCounterexample.weight <
          2 * weightedCorrectMass
            (fun x =>
              (BalancedResidualCounterexample.base x,
                BalancedResidualCounterexample.side x))
            BalancedResidualCounterexample.target
            BalancedResidualCounterexample.weight h) := by
  exact
    residualSideInformationCoverage_anchor_pure_residual_obstruction_not_sufficient_for_success

end Mettapedia.Computability.PNP.CruxSynthesisRegression
