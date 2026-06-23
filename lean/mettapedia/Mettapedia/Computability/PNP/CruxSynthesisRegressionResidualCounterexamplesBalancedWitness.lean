import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesPure
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesBalancing
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesWitnesses
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesAnySuccess

/-!
# Regression checks for PNP residual-side-information balanced prediction witnesses

This module keeps the historical `CruxSynthesisRegression` theorem namespace
while isolating the balanced prediction witness that is still insufficient for
success.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem residual_side_information_anchor_balanced_prediction_witness_not_sufficient_for_success_regression
    :
    ¬ SupportwiseSourceOnlyPairClassifier
      BalancedResidualCounterexample.base
      BalancedResidualCounterexample.side
      BalancedResidualCounterexample.weight
      BalancedResidualCounterexample.separatingClassifier ∧
      (∃ x, 0 < BalancedResidualCounterexample.weight x ∧
        BalancedResidualCounterexample.separatingClassifier
            (BalancedResidualCounterexample.base
              (BalancedResidualCounterexample.resolveSwap x),
              BalancedResidualCounterexample.side
                (BalancedResidualCounterexample.resolveSwap x)) ≠
          BalancedResidualCounterexample.separatingClassifier
            (BalancedResidualCounterexample.base x,
              BalancedResidualCounterexample.side x)) ∧
      ¬ 0 < doubledAdvantage
        (fun x =>
          (BalancedResidualCounterexample.base x,
            BalancedResidualCounterexample.side x))
        BalancedResidualCounterexample.target
        BalancedResidualCounterexample.weight
        BalancedResidualCounterexample.separatingClassifier ∧
      ¬ weightedTotalMass BalancedResidualCounterexample.weight <
        2 * weightedCorrectMass
          (fun x =>
            (BalancedResidualCounterexample.base x,
              BalancedResidualCounterexample.side x))
          BalancedResidualCounterexample.target
          BalancedResidualCounterexample.weight
          BalancedResidualCounterexample.separatingClassifier := by
  exact
    residualSideInformationCoverage_anchor_balanced_prediction_witness_not_sufficient_for_success

end Mettapedia.Computability.PNP.CruxSynthesisRegression
