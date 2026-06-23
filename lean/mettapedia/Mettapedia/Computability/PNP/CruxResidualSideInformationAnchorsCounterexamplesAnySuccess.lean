import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesWitnesses

/-!
# PNP residual-side-information anchors: full-package no-success failures

These counterexamples strengthen concrete witness failure into statements that
no classifier on the visible surface can beat chance or strict half accuracy.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: the same balanced four-point surface gives a
stronger blocker than failure of one witness classifier.  It carries a
concrete classifier with the full supported proof-relevant obstruction
package, yet no classifier on the same visible `(base, side)` surface can beat
chance or strict half accuracy at all. -/
theorem residualSideInformationCoverage_anchor_supported_obstruction_package_not_sufficient_for_any_success
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
    BalancedResidualCounterexample.supported_obstruction_package_not_sufficient_for_any_success_package

/-- Route-coverage anchor: the balanced positive-mass surface exposes the
precise missing obstruction behind the previous packet.  The same visible
surface carries a concrete classifier with the full supported obstruction
package for `resolveSwap`, but it also admits a second involution that fixes
the visible `(base, side)` pair on positive support while flipping the target.
That balancing symmetry blocks every classifier success on the surface. -/
theorem residualSideInformationCoverage_anchor_supported_obstruction_package_with_visible_pair_balancing_blocks_any_success
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
    BalancedResidualCounterexample.supported_obstruction_package_with_visiblePair_balancing_blocks_any_success_package

end Mettapedia.Computability.PNP
