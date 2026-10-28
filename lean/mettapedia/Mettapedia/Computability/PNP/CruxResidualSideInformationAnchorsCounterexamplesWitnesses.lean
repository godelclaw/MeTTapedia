import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesBalancing

/-!
# PNP residual-side-information anchors: balanced witness failures

These counterexamples show that prediction-separation witnesses and supported
obstruction packages for a concrete classifier still need the visible-balancing
obstruction ruled out.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: proof-relevant residual prediction separation is
still not enough on its own.  On the balanced four-point surface there is a
concrete classifier on `(base, side)` that is not supportwise source-only and
does change across a positive-support involution pair, yet it still cannot
obtain positive doubled advantage or strict-half accuracy. -/
theorem residualSideInformationCoverage_anchor_balanced_prediction_witness_not_sufficient_for_success
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
  exact BalancedResidualCounterexample.prediction_witness_not_sufficient_package

/-- Route-coverage anchor: even the full supported residual obstruction package
for a concrete classifier on `(base, side)` is still not enough on its own.
The balanced four-point surface has positive resolved mass and a concrete
classifier witnessing non-source-determined residual variation, failure of
supportwise source-only factoring, and prediction separation, yet that
classifier still cannot obtain positive doubled advantage or strict-half
accuracy. -/
theorem residualSideInformationCoverage_anchor_supported_obstruction_package_not_sufficient_for_success
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
  exact BalancedResidualCounterexample.supported_obstruction_package_not_sufficient_package

end Mettapedia.Computability.PNP
