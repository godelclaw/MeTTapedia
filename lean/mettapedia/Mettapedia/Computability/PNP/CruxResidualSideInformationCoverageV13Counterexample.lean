import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesPure
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesBalancing
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesWitnesses
import Mettapedia.Computability.PNP.CruxResidualSideInformationAnchorsCounterexamplesAnySuccess

/-!
# PNP residual-side-information V13 counterexample subcoverage

This module packages the balanced four-point V13 counterexample.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- The balanced four-point V13 surface carries a concrete residual-reading
classifier realizing the supported obstruction package while every classifier
on the same visible surface remains blocked by visible-pair balancing. -/
def V13ResidualSideInformationCounterexampleSubcoverage : Prop :=
  (∃ h : Unit × Bool → Bool,
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
          BalancedResidualCounterexample.weight h'))

@[simp] theorem v13ResidualSideInformationCounterexampleSubcoverage :
    V13ResidualSideInformationCounterexampleSubcoverage := by
  exact
    residualSideInformationCoverage_anchor_supported_obstruction_package_with_visible_pair_balancing_blocks_any_success

end Mettapedia.Computability.PNP
